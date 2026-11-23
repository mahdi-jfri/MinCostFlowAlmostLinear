module

public import WordRAM.LinkDefs
public import MinCostFlow.Machine.WideWord.Trie

/-!
# Compiler from `w'`-bit guest `WordRAM` programs to narrow-word host `Stmt`s

Given any guest program `Q : Program` and base procedure index `base`, `compile Q base` produces a
deterministic host procedure list (`NoRand`) at word size `w` (`2 * h + 2 ≤ w`, `w' ≤ L * h`):
* `base + 0`: `simEntry` taking `[ctrl, initLen, retDst]` (where `ctrl` holds `[root, hp, L, h, 2^h]`),
* `base + 1 .. base + 18`: `arithModule (base + 1)`,
* `base + 19 .. base + 20`: `trieModule (base + 1)`,
* `base + 21 .. base + 20 + Q.procs.length`: compiled guest procedures taking `[ctrl, retDst, framePtr]`.

Guest constants are materialized from `bitsMSB` via `mwZero` and `mwShl1AddBit` so host constants
stay bounded by `max 1 (frameSlots Q)` (plus `0`/`1` and `2`), avoiding large host literals.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

/-! ### Expression and statement temporary-slot bounds -/

/-- Number of temporary `L`-limb slots needed above `dstSlot` to evaluate `e`. -/
def exprTempDepth : Expr → ℕ
  | .const _ => 0
  | .reg _ => 0
  | .load a => exprTempDepth a
  | .bin _ a b => 3 + max (exprTempDepth a) (exprTempDepth b)

theorem exprTempDepth_le (e : Expr) : exprTempDepth e ≤ 3 * e.size := by
  induction e with
  | const _ => simp [exprTempDepth]
  | reg _ => simp [exprTempDepth]
  | load a ih => simp [exprTempDepth, Expr.size]; omega
  | bin _ a b iha ihb => simp [exprTempDepth, Expr.size]; omega

/-- Number of temporary `L`-limb slots needed above `Q.regBound` across an argument list. -/
def argsTempDepth : List Expr → ℕ
  | [] => 0
  | e :: es => max (exprTempDepth e) (argsTempDepth es)

theorem argsTempDepth_le (args : List Expr) : argsTempDepth args ≤ 3 * argsSize args := by
  induction args with
  | nil => simp [argsTempDepth]
  | cons e es ih =>
    simp only [argsTempDepth, argsSize]
    have he := exprTempDepth_le e
    omega

/-- Number of temporary `L`-limb slots needed above `Q.regBound` by statement `s`. -/
def stmtTempDepth : Stmt → ℕ
  | .nop => 0
  | .assign _ e => 1 + exprTempDepth e
  | .store a e => 2 + max (exprTempDepth a) (exprTempDepth e)
  | .rand _ => 0
  | .seq s t => max (stmtTempDepth s) (stmtTempDepth t)
  | .cond e s t => max (1 + exprTempDepth e) (max (stmtTempDepth s) (stmtTempDepth t))
  | .loop e body => max (1 + exprTempDepth e) (stmtTempDepth body)
  | .call _ _ args => 1 + argsTempDepth args
  | .ret e => 1 + exprTempDepth e

/-- Upper bound on temporary `L`-limb slots used by any procedure of `Q`. -/
def programTempBound (Q : Program) : ℕ :=
  Q.procs.foldr (fun s acc => max (stmtTempDepth s) acc) 0

/-- Total number of `L`-limb words in every compiled guest call frame of `Q`. -/
def frameSlots (Q : Program) : ℕ :=
  Q.regBound + max 1 (programTempBound Q)

private theorem stmtTempDepth_le_foldr {s : Stmt} :
    ∀ {ps : List Stmt}, s ∈ ps →
      stmtTempDepth s ≤ ps.foldr (fun t acc => max (stmtTempDepth t) acc) 0
  | [], h => by simp at h
  | p :: ps, h => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_max_left _ _
    · exact le_trans (stmtTempDepth_le_foldr h') (le_max_right _ _)

theorem le_programTempBound {Q : Program} {s : Stmt} (hs : s ∈ Q.procs) :
    stmtTempDepth s ≤ programTempBound Q :=
  stmtTempDepth_le_foldr hs

private theorem regBound_le_foldr {s : Stmt} :
    ∀ {ps : List Stmt}, s ∈ ps →
      s.regBound ≤ ps.foldr (fun t acc => max t.regBound acc) 0
  | [], h => by simp at h
  | p :: ps, h => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_max_left _ _
    · exact le_trans (regBound_le_foldr h') (le_max_right _ _)

theorem stmt_regBound_le_program {Q : Program} {s : Stmt} (hs : s ∈ Q.procs) :
    s.regBound ≤ Q.regBound :=
  le_trans (regBound_le_foldr hs) (le_max_right _ _)

theorem one_le_program_regBound (Q : Program) : 1 ≤ Q.regBound :=
  le_max_left _ _

theorem one_le_max_tempBound (Q : Program) : 1 ≤ max 1 (programTempBound Q) :=
  le_max_left _ _

theorem frameSlots_ge (Q : Program) : Q.regBound + 1 ≤ frameSlots Q :=
  Nat.add_le_add_left (le_max_left _ _) _

/-- Shared polynomial time/space scale constant `K_Q` for `Q`. -/
def simScale (Q : Program) : ℕ :=
  frameSlots Q + 1000

theorem frameSlots_lt_simScale (Q : Program) : frameSlots Q < simScale Q := by
  dsimp only [simScale]; omega

/-! ### Host code generation -/

/-- Host address expression for `L`-limb slot `slot` inside frame register `rBase`, using `reg 5 = L`. -/
def slotAddr (rBase slot : ℕ) : Expr :=
  .bin .add (.reg rBase) (.bin .mul (.const slot) (.reg 5))

/-- Materialize constant `k` MSB-first via `mwZero` and `mwShl1AddBit` at frame slot `dstSlot`. -/
def compileConstBits (arithBase dstSlot k : ℕ) : Stmt :=
  (bitsMSB k).foldl
    (fun acc b =>
      acc ;; .call 8 (arithBase + idxShl1AddBit)
        [slotAddr 2 dstSlot, .const b, .reg 5, .reg 7])
    (.call 8 (arithBase + idxZero) [slotAddr 2 dstSlot, .reg 5])

/-- Apply guest binary operator `op` to slots `aSlot` and `bSlot`, writing result into `dstSlot`
using `scratchSlot` when calling `mwDivMod`. -/
def compileBinOp (arithBase : ℕ) (op : BinOp) (aSlot bSlot dstSlot scratchSlot : ℕ) : Stmt :=
  match op with
  | .add => .call 8 (arithBase + idxAdd)
      [slotAddr 2 aSlot, slotAddr 2 bSlot, slotAddr 2 dstSlot, .reg 5, .reg 7]
  | .sub => .call 8 (arithBase + idxSub)
      [slotAddr 2 aSlot, slotAddr 2 bSlot, slotAddr 2 dstSlot, .reg 5, .reg 7]
  | .mul => .call 8 (arithBase + idxMul)
      [slotAddr 2 aSlot, slotAddr 2 bSlot, slotAddr 2 dstSlot, .reg 5, .reg 7]
  | .div => .call 8 (arithBase + idxDivMod)
      [slotAddr 2 aSlot, slotAddr 2 bSlot, slotAddr 2 dstSlot, slotAddr 2 scratchSlot, .reg 5, .reg 6, .reg 7]
  | .mod => .call 8 (arithBase + idxDivMod)
      [slotAddr 2 aSlot, slotAddr 2 bSlot, slotAddr 2 scratchSlot, slotAddr 2 dstSlot, .reg 5, .reg 6, .reg 7]
  | .lt => .call 8 (arithBase + idxLt) [slotAddr 2 aSlot, slotAddr 2 bSlot, .reg 5] ;;
           .call 8 (arithBase + idxFromHost) [.reg 8, slotAddr 2 dstSlot, .reg 5, .reg 7]
  | .eq => .call 8 (arithBase + idxEq) [slotAddr 2 aSlot, slotAddr 2 bSlot, .reg 5] ;;
           .call 8 (arithBase + idxFromHost) [.reg 8, slotAddr 2 dstSlot, .reg 5, .reg 7]
  | .and => .call 8 (arithBase + idxAnd)
      [slotAddr 2 aSlot, slotAddr 2 bSlot, slotAddr 2 dstSlot, .reg 5]
  | .or => .call 8 (arithBase + idxOr)
      [slotAddr 2 aSlot, slotAddr 2 bSlot, slotAddr 2 dstSlot, .reg 5]
  | .xor => .call 8 (arithBase + idxXor)
      [slotAddr 2 aSlot, slotAddr 2 bSlot, slotAddr 2 dstSlot, .reg 5]
  | .shiftLeft => .call 8 (arithBase + idxShiftLeft)
      [slotAddr 2 aSlot, slotAddr 2 bSlot, slotAddr 2 dstSlot, .reg 5, .reg 6, .reg 7]
  | .shiftRight => .call 8 (arithBase + idxShiftRight)
      [slotAddr 2 aSlot, slotAddr 2 bSlot, slotAddr 2 dstSlot, .reg 5, .reg 6, .reg 7]

/-- Compile guest expression `e` into frame slot `dstSlot`, using temporaries starting at
`tmpSlot` (`dstSlot < tmpSlot`). -/
def compileExpr (arithBase trieBase dstSlot tmpSlot : ℕ) : Expr → Stmt
  | .const k => compileConstBits arithBase dstSlot k
  | .reg r => .call 8 (arithBase + idxCopy) [slotAddr 2 r, slotAddr 2 dstSlot, .reg 5]
  | .load a =>
    compileExpr arithBase trieBase dstSlot tmpSlot a ;;
    .assign 8 (.load (.reg 3)) ;;
    .call 8 (trieBase + idxTrieRead) [.reg 8, slotAddr 2 dstSlot, slotAddr 2 dstSlot, .reg 5]
  | .bin op a b =>
    compileExpr arithBase trieBase tmpSlot (tmpSlot + 3) a ;;
    compileExpr arithBase trieBase (tmpSlot + 1) (tmpSlot + 3) b ;;
    compileBinOp arithBase op tmpSlot (tmpSlot + 1) dstSlot (tmpSlot + 2)

/-- Compile call argument expressions into callee frame slots `idx, idx + 1, ...` starting at
host address in `reg rCallee`, using caller temporary area `[baseSlot ..)`. -/
def compileCallArgs (arithBase trieBase baseSlot rCallee : ℕ) : ℕ → List Expr → Stmt
  | _, [] => .nop
  | idx, e :: es =>
    compileExpr arithBase trieBase baseSlot (baseSlot + 1) e ;;
    .call 8 (arithBase + idxCopy) [slotAddr 2 baseSlot, slotAddr rCallee idx, .reg 5] ;;
    compileCallArgs arithBase trieBase baseSlot rCallee (idx + 1) es

/-- Compile guest statement `s` at control-flow nesting depth `depth` (`16 + depth` is reserved
exclusively for the loop flag or callee frame pointer of this node). Note guest `.rand r` sets
register `r` to `0` (simulating all-false random tape `ω₀ = fun _ => false`). -/
def compileStmt (Q : Program) (arithBase trieBase procBase : ℕ) : ℕ → Stmt → Stmt
  | _, .nop => .nop
  | _, .assign r e =>
    let b := Q.regBound
    compileExpr arithBase trieBase b (b + 1) e ;;
    .call 8 (arithBase + idxCopy) [slotAddr 2 b, slotAddr 2 r, .reg 5]
  | _, .store a e =>
    let b := Q.regBound
    compileExpr arithBase trieBase b (b + 2) a ;;
    compileExpr arithBase trieBase (b + 1) (b + 2) e ;;
    .call 8 (trieBase + idxTrieWrite)
      [.reg 3, .reg 4, slotAddr 2 b, slotAddr 2 (b + 1), .reg 5, .reg 7]
  | _, .rand r =>
    .call 8 (arithBase + idxZero) [slotAddr 2 r, .reg 5]
  | d, .seq s t =>
    compileStmt Q arithBase trieBase procBase d s ;;
    compileStmt Q arithBase trieBase procBase d t
  | d, .cond e s t =>
    let b := Q.regBound
    compileExpr arithBase trieBase b (b + 1) e ;;
    .call 8 (arithBase + idxIsZero) [slotAddr 2 b, .reg 5] ;;
    .cond (.reg 8)
      (compileStmt Q arithBase trieBase procBase d t)
      (compileStmt Q arithBase trieBase procBase d s)
  | d, .loop e body =>
    let b := Q.regBound
    let rFlag := 16 + d
    compileExpr arithBase trieBase b (b + 1) e ;;
    .call 8 (arithBase + idxIsZero) [slotAddr 2 b, .reg 5] ;;
    .assign rFlag (.bin .eq (.reg 8) (.const 0)) ;;
    .loop (.reg rFlag)
      (compileStmt Q arithBase trieBase procBase (d + 1) body ;;
       compileExpr arithBase trieBase b (b + 1) e ;;
       .call 8 (arithBase + idxIsZero) [slotAddr 2 b, .reg 5] ;;
       .assign rFlag (.bin .eq (.reg 8) (.const 0)))
  | d, .call r f args =>
    let b := Q.regBound
    let rCallee := 16 + d
    .assign rCallee (.load (.reg 4)) ;;
    .store (.reg 4) (.bin .add (.reg rCallee) (.bin .mul (.const (frameSlots Q)) (.reg 5))) ;;
    compileCallArgs arithBase trieBase b rCallee 0 args ;;
    .call 8 (procBase + f) [.reg 0, slotAddr 2 r, .reg rCallee]
  | _, .ret e =>
    let b := Q.regBound
    compileExpr arithBase trieBase b (b + 1) e ;;
    .call 8 (arithBase + idxCopy) [slotAddr 2 b, .reg 1, .reg 5] ;;
    .ret (.const 0)

/-- Compiled body of a guest procedure taking `[ctrl, retDst, framePtr]`.
Falls through to zeroing `retDst` if the guest body exits normally without `.ret`. -/
def compileProc (Q : Program) (arithBase trieBase procBase : ℕ) (body : Stmt) : Stmt :=
  .assign 3 (.reg 0) ;;
  .assign 4 (.bin .add (.reg 0) (.const 1)) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const 2))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const 4))) ;;
  compileStmt Q arithBase trieBase procBase 0 body ;;
  .call 8 (arithBase + idxZero) [.reg 1, .reg 5] ;;
  .ret (.const 0)

/-- Entry procedure placed at `base + 0`: takes `[ctrl, initLen, retDst]`, allocates the entry
frame for guest procedure `0`, writes `initLen` into guest register `0`, calls compiled
procedure `0`, and returns `0`. -/
def simEntry (Q : Program) (arithBase procBase : ℕ) : Stmt :=
  .assign 3 (.bin .add (.reg 0) (.const 1)) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const 2))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const 4))) ;;
  .assign 6 (.load (.reg 3)) ;;
  .store (.reg 3) (.bin .add (.reg 6) (.bin .mul (.const (frameSlots Q)) (.reg 4))) ;;
  .call 8 (arithBase + idxFromHost) [.reg 1, .reg 6, .reg 4, .reg 5] ;;
  .call 8 (procBase + 0) [.reg 0, .reg 2, .reg 6] ;;
  .ret (.const 0)

/-- Compile guest program `Q` into a relocatable module starting at host procedure index `base`. -/
def compile (Q : Program) (base : ℕ) : List Stmt :=
  [simEntry Q (base + 1) (base + 21)] ++
    arithModule (base + 1) ++
    trieModule (base + 1) ++
    Q.procs.map (compileProc Q (base + 1) (base + 19) (base + 21))

/-- Standalone deterministic host program compiling `Q` at procedure index `0`. -/
def compileProgram (Q : Program) : Program :=
  ⟨compile Q 0⟩

/-! ### Layout and determinism lemmas -/

theorem compile_length (Q : Program) (base : ℕ) :
    (compile Q base).length = 21 + Q.procs.length := by
  simp only [compile, List.length_append, List.length_singleton, arithModule_length,
    trieModule_length, List.length_map]

theorem arithModule_hasAt_of_compile {p : Program} {Q : Program} {b : ℕ}
    (hp : p.HasAt b (compile Q b)) : p.HasAt (b + 1) (arithModule (b + 1)) := by
  intro k hk
  have h18 : k < 18 := by simpa [arithModule_length] using hk
  have htot : 1 + k < (compile Q b).length := by
    rw [compile_length]; omega
  have h := hp (1 + k) htot
  rw [← Nat.add_assoc] at h
  have hc : (compile Q b)[1 + k]? = some (arithModule (b + 1))[k] := by
    dsimp only [compile]
    rw [List.append_assoc, List.append_assoc, show 1 + k = k + 1 by omega]
    simp only [List.singleton_append, List.getElem?_cons_succ]
    rw [List.getElem?_append_left hk, List.getElem?_eq_getElem hk]; rfl
  rw [List.getElem?_eq_getElem htot] at hc
  have h2 := Option.some.inj hc
  rwa [h2] at h

theorem trieModule_hasAt_of_compile {p : Program} {Q : Program} {b : ℕ}
    (hp : p.HasAt b (compile Q b)) : p.HasAt (b + 19) (trieModule (b + 1)) := by
  intro k hk
  have h2 : k < 2 := by simpa [trieModule_length] using hk
  have htot : 19 + k < (compile Q b).length := by
    rw [compile_length]; omega
  have h := hp (19 + k) htot
  have hc : (compile Q b)[19 + k]? = some (trieModule (b + 1))[k] := by
    dsimp only [compile]
    rw [List.append_assoc, List.append_assoc, show 19 + k = 18 + k + 1 by omega]
    simp only [List.singleton_append, List.getElem?_cons_succ]
    rw [List.getElem?_append_right (by rw [arithModule_length]; omega)]
    rw [arithModule_length, show 18 + k - 18 = k by omega]
    rw [List.getElem?_append_left hk, List.getElem?_eq_getElem hk]; rfl
  rw [List.getElem?_eq_getElem htot] at hc
  have h3 := Option.some.inj hc
  rwa [show b + (19 + k) = b + 19 + k by omega, h3] at h

theorem simEntry_procs_at {p : Program} {Q : Program} {b : ℕ}
    (hp : p.HasAt b (compile Q b)) :
    p.procs[b]? = some (simEntry Q (b + 1) (b + 21)) := by
  have h := hp 0 (by rw [compile_length]; omega)
  simpa [compile] using h

theorem compileProc_procs_at {p : Program} {Q : Program} {b f : ℕ} {body : Stmt}
    (hp : p.HasAt b (compile Q b)) (hf : Q.procs[f]? = some body) :
    p.procs[b + 21 + f]? = some (compileProc Q (b + 1) (b + 19) (b + 21) body) := by
  have hlt : f < Q.procs.length := by
    by_contra hge
    simp [List.getElem?_eq_none (Nat.not_lt.mp hge)] at hf
  have htot : 21 + f < (compile Q b).length := by
    rw [compile_length]; omega
  have h := hp (21 + f) htot
  have hc : (compile Q b)[21 + f]? = some (compileProc Q (b + 1) (b + 19) (b + 21) body) := by
    dsimp only [compile]
    rw [List.append_assoc, List.append_assoc, show 21 + f = 20 + f + 1 by omega]
    simp only [List.singleton_append, List.getElem?_cons_succ]
    rw [List.getElem?_append_right (by rw [arithModule_length]; omega)]
    rw [arithModule_length, show 20 + f - 18 = 2 + f by omega]
    rw [List.getElem?_append_right (by rw [trieModule_length]; omega)]
    rw [trieModule_length, show 2 + f - 2 = f by omega]
    rw [List.getElem?_map, hf]
    rfl
  rw [List.getElem?_eq_getElem htot] at hc
  have h2 := Option.some.inj hc
  rwa [show b + (21 + f) = b + 21 + f by omega, h2] at h

private theorem foldl_bits_noRand (arithBase dstSlot : ℕ) (bits : List ℕ) (acc : Stmt)
    (hacc : acc.NoRand) :
    (bits.foldl
      (fun acc b =>
        acc ;; .call 8 (arithBase + idxShl1AddBit)
          [slotAddr 2 dstSlot, .const b, .reg 5, .reg 7])
      acc).NoRand := by
  induction bits generalizing acc with
  | nil => exact hacc
  | cons b bs ih =>
    apply ih
    exact ⟨hacc, trivial⟩

theorem compileConstBits_noRand (arithBase dstSlot k : ℕ) :
    (compileConstBits arithBase dstSlot k).NoRand :=
  foldl_bits_noRand arithBase dstSlot (bitsMSB k) _ trivial

theorem compileBinOp_noRand (arithBase : ℕ) (op : BinOp) (aSlot bSlot dstSlot scratchSlot : ℕ) :
    (compileBinOp arithBase op aSlot bSlot dstSlot scratchSlot).NoRand := by
  cases op <;> simp [compileBinOp, Stmt.NoRand]

theorem compileExpr_noRand (arithBase trieBase dstSlot tmpSlot : ℕ) (e : Expr) :
    (compileExpr arithBase trieBase dstSlot tmpSlot e).NoRand := by
  induction e generalizing dstSlot tmpSlot with
  | const k => exact compileConstBits_noRand _ _ k
  | reg r => simp [compileExpr, Stmt.NoRand]
  | load a ih => exact ⟨ih dstSlot tmpSlot, ⟨trivial, trivial⟩⟩
  | bin op a b iha ihb =>
    exact ⟨iha tmpSlot (tmpSlot + 3), ⟨ihb (tmpSlot + 1) (tmpSlot + 3),
      compileBinOp_noRand _ op _ _ _ _⟩⟩

theorem compileCallArgs_noRand (arithBase trieBase baseSlot rCallee idx : ℕ) (args : List Expr) :
    (compileCallArgs arithBase trieBase baseSlot rCallee idx args).NoRand := by
  induction args generalizing idx with
  | nil => simp [compileCallArgs, Stmt.NoRand]
  | cons e es ih =>
    exact ⟨compileExpr_noRand _ _ _ _ e, ⟨trivial, ih (idx + 1)⟩⟩

theorem compileStmt_noRand (Q : Program) (arithBase trieBase procBase depth : ℕ) (s : Stmt) :
    (compileStmt Q arithBase trieBase procBase depth s).NoRand := by
  induction s generalizing depth with
  | nop => trivial
  | assign r e => exact ⟨compileExpr_noRand _ _ _ _ e, trivial⟩
  | store a e => exact ⟨compileExpr_noRand _ _ _ _ a, ⟨compileExpr_noRand _ _ _ _ e, trivial⟩⟩
  | rand r => trivial
  | seq s t ihs iht => exact ⟨ihs depth, iht depth⟩
  | cond e s t ihs iht => exact ⟨compileExpr_noRand _ _ _ _ e, ⟨trivial, ⟨iht depth, ihs depth⟩⟩⟩
  | loop e body ih =>
    exact ⟨compileExpr_noRand _ _ _ _ e, ⟨trivial, ⟨trivial,
      ⟨ih (depth + 1), ⟨compileExpr_noRand _ _ _ _ e, ⟨trivial, trivial⟩⟩⟩⟩⟩⟩
  | call r f args =>
    exact ⟨trivial, ⟨trivial, ⟨compileCallArgs_noRand _ _ _ _ 0 args, trivial⟩⟩⟩
  | ret e => exact ⟨compileExpr_noRand _ _ _ _ e, ⟨trivial, trivial⟩⟩

theorem compileProc_noRand (Q : Program) (arithBase trieBase procBase : ℕ) (body : Stmt) :
    (compileProc Q arithBase trieBase procBase body).NoRand := by
  exact ⟨trivial, ⟨trivial, ⟨trivial, ⟨trivial, ⟨trivial,
    ⟨compileStmt_noRand Q arithBase trieBase procBase 0 body, ⟨trivial, trivial⟩⟩⟩⟩⟩⟩⟩

theorem simEntry_noRand (Q : Program) (arithBase procBase : ℕ) :
    (simEntry Q arithBase procBase).NoRand := by
  simp [simEntry, Stmt.NoRand]

theorem compile_noRand (Q : Program) (base : ℕ) :
    ∀ s ∈ compile Q base, s.NoRand := by
  intro s hs
  simp only [compile, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map] at hs
  rcases hs with ((rfl | hs) | hs) | ⟨body, _, rfl⟩
  · exact simEntry_noRand Q _ _
  · exact arithModule_noRand _ s hs
  · exact trieModule_noRand _ s hs
  · exact compileProc_noRand Q _ _ _ body

theorem compileProgram_isDeterministic (Q : Program) :
    (compileProgram Q).IsDeterministic :=
  compile_noRand Q 0

end MinCostFlow.WideWord