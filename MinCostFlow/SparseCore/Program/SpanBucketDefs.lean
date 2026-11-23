module

public import MinCostFlow.SparseCore.Program.SpanModule
public import MinCostFlow.SparseCore.Program.SpanPhaseBase
public import MinCostFlow.SparseCore.Program.SpanReadout

/-!
# Multi-Bucket Dynamic Spanner Manager: Definitions (`SpanBucketDefs`)

Packages a table of up to `cap` independent `dynSpannerDS P` instances — one per active
`(component, bucket)` slot of a branch in `BundleTreeState` (Lemma 5.17, page 23) — as a single
deterministic `WordRAM.DataStructure` (`bucketSpannerDS P cap`) implemented by a single relocatable
procedure table `bucketSpannerProcs impl b`.

* **Abstract state** (`BucketSpannerState cap := Fin cap → Option DSHist`): each slot is either
  `none` (uninitialized / lazy) or `some s`, representing the model state `s.state P :
  DynSpannerState P.L` (`SpanBridge.lean`).
* **Operations**:
  - `init [cap, h]`: allocates the `cap`-word zero-initialized handle table at `h` (space `cap`,
    cost `10`).
  - `op 0` (activate / restart `[tbl, slot, L, splitB, vCap, eCap, nV, V_ptr, nE, E_ptr, h]`):
    computes `q = phaseBase (nV + splitB) L`, runs `dsInitStmt` at `h`, stores handle `h` into
    `mem[tbl + slot]`, and returns the new heap pointer. Works uniformly for both lazy first
    initialization (`stepBundleTree`) and branch restart (`restartBundleTree`).
  - `op 1` (update `[tbl, slot, batchPtr, W, h]`): loads handle `b = mem[tbl + slot]`, calls
    `dsUpdateOpStmt [b, batchPtr, W, h]`, and returns the new heap pointer, leaving the batch
    output header `[uhOutPtr, |U_H|, words, dOutPtr, |D|]` at `h + W`.
  - `op 2` (read `H` pointer `[tbl, slot, h]`): stores `dsHPtr b vCap eCap` at `h` (with
    `DynGraphAt` for `(s.state P).H`), returns `h + 1`.
  - `op 3` (read `G` pointer `[tbl, slot, h]`): stores `dsGPtr b` at `h` (with `DynGraphAt` for
    `(s.state P).G`), returns `h + 1`.
  - `op 4` (read `piTotal` walk pointer `[tbl, slot, e, h]`): stores the walk pointer of
    `piTotal (s.state P) e` at `h`, returns `h + 1`.
* **Costs**: as in `dynSpannerDS`, the cost of an update is amortized
  (`dsUpdateAmortCost`). The potential is the sum of the banks `DSHist.bank` of the active slots
  (`bucketPhi`).

Verification (`bucketSpannerDS_implements`) is in `SpanBucket.lean`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## Procedure offsets and bodies -/

def bsOffParam : ℕ := 0
def bsOffRead : ℕ := 3
def bsOffOps : ℕ := 6
def bsOffDyn : ℕ := 12

def bsIdxInit : ℕ := bsOffOps + 0
def bsIdxOp0 : ℕ := bsOffOps + 1

/-- `args = [cap, h]`: allocates a `cap`-word zero-initialized handle table at `h` (relying on
`ZeroFrom mem h`) and returns `h + cap`. -/
def bucketSpanInitStmt : Stmt :=
  .ret (.bin .add (.reg 1) (.reg 0))

/-- `args = [tbl, slot, L, splitB, vCap, eCap, nV, V_ptr, nE, E_ptr, h]`: computes
`q := phaseBase (nV + splitB) L`, initializes a `dynSpannerDS` instance at handle `h`, stores `h`
into `mem[tbl + slot]`, and returns the new heap pointer. -/
def bucketSpanActivateStmt (bPhaseBase bDSInit : ℕ) : Stmt :=
  .call 11 bPhaseBase [.bin .add (.reg 6) (.reg 3), .reg 2] ;;
  .call 12 bDSInit
    [.reg 2, .reg 11, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10] ;;
  .store (.bin .add (.reg 0) (.reg 1)) (.reg 10) ;;
  .ret (.reg 12)

/-- `args = [tbl, slot, batchPtr, W, h]`: loads handle `b := mem[tbl + slot]`, runs
`dsUpdateOpStmt [b, batchPtr, W, h]`, and returns the new heap pointer. -/
def bucketSpanUpdateStmt (bDSUpdate : ℕ) : Stmt :=
  .assign 5 (.load (.bin .add (.reg 0) (.reg 1))) ;;
  .call 6 bDSUpdate [.reg 5, .reg 2, .reg 3, .reg 4] ;;
  .ret (.reg 6)

/-- `args = [tbl, slot, h]`: loads handle `b := mem[tbl + slot]`, computes `dsHPtr b vCap eCap`,
stores it at `h`, and returns `h + 1`. -/
def bucketSpanReadHStmt (bHPtr : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.reg 1))) ;;
  .call 4 bHPtr [.reg 3] ;;
  .store (.reg 2) (.reg 4) ;;
  .ret (.bin .add (.reg 2) (.const 1))

/-- `args = [tbl, slot, h]`: loads handle `b := mem[tbl + slot]`, computes `dsGPtr b`, stores it
at `h`, and returns `h + 1`. -/
def bucketSpanReadGStmt (bGPtr : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.reg 1))) ;;
  .call 4 bGPtr [.reg 3] ;;
  .store (.reg 2) (.reg 4) ;;
  .ret (.bin .add (.reg 2) (.const 1))

/-- `args = [tbl, slot, e, h]`: loads handle `b := mem[tbl + slot]`, computes the `piTotal` walk
pointer for edge `e`, stores it at `h`, and returns `h + 1`. -/
def bucketSpanReadPiStmt (bPiPtr : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.reg 1))) ;;
  .call 5 bPiPtr [.reg 4, .reg 2] ;;
  .store (.reg 3) (.reg 5) ;;
  .ret (.bin .add (.reg 3) (.const 1))

/-- The 6 wrapper procedures of `bucketSpannerDS` (`init` and operations `0..4`). -/
def bucketSpanOpsProcs (b : ℕ) : List Stmt :=
  [bucketSpanInitStmt,
   bucketSpanActivateStmt (b + bsOffParam + spanParamIdxPhaseBase)
     (b + bsOffDyn + dynSpannerInitOff),
   bucketSpanUpdateStmt (b + bsOffDyn + dynSpannerUpdateOff),
   bucketSpanReadHStmt (b + bsOffRead + spanReadIdxHPtr),
   bucketSpanReadGStmt (b + bsOffRead + spanReadIdxGPtr),
   bucketSpanReadPiStmt (b + bsOffRead + spanReadIdxPiWalkPtr)]

/-- Complete relocatable deterministic procedure list for `bucketSpannerDS`, anchored at `b`. -/
def bucketSpannerProcs (impl : SparsifyImpl) (b : ℕ) : List Stmt :=
  spanParamProcs (b + bsOffParam) ++
  spanReadoutProcs ++
  bucketSpanOpsProcs b ++
  dynSpannerDSProcs impl (b + bsOffDyn)

/-! ## Abstract state and `WordRAM.DataStructure` specification -/

/-- Abstract state of `bucketSpannerDS`: each slot `j : Fin cap` is either uninitialized (`none`)
or holds a dynamic spanner history `some s`. -/
abbrev BucketSpannerState (cap : ℕ) := Fin cap → Option DSHist

/-- Update slot `j` in a `BucketSpannerState` to `val`. -/
def BucketSpannerState.set {cap : ℕ} (S : BucketSpannerState cap) (j : Fin cap)
    (val : Option DSHist) : BucketSpannerState cap :=
  Function.update S j val

/-- The `dynSpannerDS` initialization arguments constructed by operation `0` from
`[tbl, slot, L, splitB, vCap, eCap, nV, V_ptr, nE, E_ptr, h]`. -/
noncomputable def bucketActInitArgs (args : List ℕ) : List ℕ :=
  let L := args.getD 2 0
  let splitB := args.getD 3 0
  let nV := args.getD 6 0
  [L, phaseBase (nV + splitB) L, args.getD 4 0, args.getD 5 0, nV, args.getD 7 0,
    args.getD 8 0, args.getD 9 0, args.getD 10 0]

/-- Precondition of operation `0` (activate / restart bucket):
`args = [tbl, slot, P.L, P.splitBound, P.vCap, P.eCap, nV, V_ptr, nE, E_ptr, h]`. -/
def BucketActivatePre (P : DSParams) (cap : ℕ) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ tbl slot nV V_ptr nE E_ptr h,
    args = [tbl, slot, P.L, P.splitBound, P.vCap, P.eCap, nV, V_ptr, nE, E_ptr, h] ∧
    slot < cap ∧
    nV + P.splitBound + 2 < 2 ^ P.w ∧
    DSInitPre P (bucketActInitArgs args) mem

/-- Postcondition of operation `0`: slot `slot` now holds `some ⟨G₀, []⟩` meeting
`Theorem82Clauses`, and all other slots are unchanged. -/
def BucketActivatePost (P : DSParams) (cap : ℕ) (S : BucketSpannerState cap)
    (args : List ℕ) (mem : ℕ → ℕ) (S' : BucketSpannerState cap) : Prop :=
  ∃ hslot : args.getD 1 0 < cap,
    let G := initArgsGraph (bucketActInitArgs args) mem
    S' = S.set ⟨args.getD 1 0, hslot⟩ (some ⟨G, []⟩) ∧
    Theorem82Clauses G P.L P.splitBound (dsSparsifyParams P) (canonicalSparsify P.impl) []

/-- Precondition of operation `1` (update bucket):
`args = [tbl, slot, batchPtr, W, h]`, slot is active with history `s`, and `DSUpdatePre` holds. -/
def BucketUpdatePre (P : DSParams) (cap : ℕ) (S : BucketSpannerState cap)
    (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ tbl slot batchPtr W h,
    args = [tbl, slot, batchPtr, W, h] ∧
    ∃ (hslot : slot < cap) (s : DSHist),
      S ⟨slot, hslot⟩ = some s ∧
      DSUpdatePre P s [0, batchPtr, W, h] mem

/-- Postcondition of operation `1`: slot `slot` advances from `some s` to `some s'` satisfying
`DSUpdatePost` (leaving the batch output header `[uhOutPtr, |U_H|, words, dOutPtr, |D|]` at
`h + W`), and all other slots are unchanged. -/
def BucketUpdatePost (P : DSParams) (cap : ℕ) (S : BucketSpannerState cap)
    (args : List ℕ) (mem : ℕ → ℕ) (S' : BucketSpannerState cap) (mem' : ℕ → ℕ) : Prop :=
  ∃ (hslot : args.getD 1 0 < cap) (s s' : DSHist),
    S ⟨args.getD 1 0, hslot⟩ = some s ∧
    S' = S.set ⟨args.getD 1 0, hslot⟩ (some s') ∧
    DSUpdatePost P s [0, args.getD 2 0, args.getD 3 0, args.getD 4 0] mem s' mem'

/-- Precondition of operations `2` and `3` (`readH`, `readG`): `[tbl, slot, h]` with active slot. -/
def BucketReadGraphPre (P : DSParams) (cap : ℕ) (S : BucketSpannerState cap)
    (args : List ℕ) : Prop :=
  ∃ tbl slot h, args = [tbl, slot, h] ∧ 16 ≤ 2 ^ P.w ∧
    ∃ (hslot : slot < cap) (s : DSHist), S ⟨slot, hslot⟩ = some s

/-- Precondition of operation `4` (`readPi`): `[tbl, slot, e, h]` with active slot and
`e ∈ (s.state P).G.E`. -/
def BucketReadPiPre (P : DSParams) (cap : ℕ) (S : BucketSpannerState cap)
    (args : List ℕ) : Prop :=
  ∃ tbl slot e h, args = [tbl, slot, e, h] ∧ 16 ≤ 2 ^ P.w ∧
    ∃ (hslot : slot < cap) (s : DSHist), S ⟨slot, hslot⟩ = some s ∧ e ∈ (s.state P).G.E

/-- Amortized cost bound of operation `1` (update bucket): the amortized cost
`dsUpdateAmortCost` of the update of the slot, plus `20`. -/
noncomputable def bucketUpdateCost (P : DSParams) (cap : ℕ) (S : BucketSpannerState cap)
    (args : List ℕ) (mem : ℕ → ℕ) : ℕ :=
  if hslot : args.getD 1 0 < cap then
    match S ⟨args.getD 1 0, hslot⟩ with
    | some s => dsUpdateAmortCost P s [0, args.getD 2 0, args.getD 3 0, args.getD 4 0] mem + 20
    | none => 0
  else 0

/-- Space bound of operation `1` (update bucket). -/
noncomputable def bucketUpdateSpace (P : DSParams) (cap : ℕ) (S : BucketSpannerState cap)
    (args : List ℕ) (mem : ℕ → ℕ) : ℕ :=
  if hslot : args.getD 1 0 < cap then
    match S ⟨args.getD 1 0, hslot⟩ with
    | some s => dsUpdateOpSpace P s [0, args.getD 2 0, args.getD 3 0, args.getD 4 0] mem
    | none => 0
  else 0

/-- **The multi-bucket dynamic spanner data structure** (`cap` independent `dynSpannerDS P`
slots). -/
noncomputable def bucketSpannerDS (P : DSParams) (cap : ℕ) :
    DataStructure (BucketSpannerState cap) where
  initPre args _ := ∃ h, args = [cap, h] ∧ 16 ≤ 2 ^ P.w
  initPost _ _ S _ := S = fun _ => none
  initCost _ _ := 10
  initSpace _ _ := cap
  pre i S args mem := match i with
    | 0 => BucketActivatePre P cap args mem
    | 1 => BucketUpdatePre P cap S args mem
    | 2 | 3 => BucketReadGraphPre P cap S args
    | 4 => BucketReadPiPre P cap S args
    | _ => False
  post i S args mem S' mem' := match i with
    | 0 => BucketActivatePost P cap S args mem S'
    | 1 => BucketUpdatePost P cap S args mem S' mem'
    | 2 => S' = S ∧ ∃ (hslot : args.getD 1 0 < cap) (s : DSHist),
        S ⟨args.getD 1 0, hslot⟩ = some s ∧
        DynGraphAt mem' (mem' (heapArg args)) P.vCap P.eCap (s.state P).H
    | 3 => S' = S ∧ ∃ (hslot : args.getD 1 0 < cap) (s : DSHist),
        S ⟨args.getD 1 0, hslot⟩ = some s ∧
        DynGraphAt mem' (mem' (heapArg args)) P.vCap P.eCap (s.state P).G
    | 4 => S' = S ∧ ∃ (hslot : args.getD 1 0 < cap) (s : DSHist),
        S ⟨args.getD 1 0, hslot⟩ = some s ∧
        MWalkAt mem' (mem' (heapArg args)) (piTotal (s.state P) (args.getD 2 0))
    | _ => False
  cost i S args mem := match i with
    | 0 =>
        phaseBaseCost (args.getD 6 0 + P.splitBound) P.L +
          (dynSpannerDS P).initCost (bucketActInitArgs args) mem + 35
    | 1 => bucketUpdateCost P cap S args mem
    | 2 => 60
    | 3 => 35
    | 4 => spanPiWalkPtrCost P.L + 30
    | _ => 0
  space i S args mem := match i with
    | 0 => (dynSpannerDS P).initSpace (bucketActInitArgs args) mem
    | 1 => bucketUpdateSpace P cap S args mem
    | 2 | 3 | 4 => 1
    | _ => 0

/-! ## Concrete state, footprint, and `DSRep` -/

/-- Concrete metadata of `bucketSpannerDS`: for each slot, either `none` or its handle and the
concrete state of `dynSpannerRep` (the history and the `DynSpannerMeta`). -/
structure BucketSpannerMeta (L cap : ℕ) where
  slots : Fin cap → Option (ℕ × DSHist × DynSpannerMeta L)

/-- Update slot `j` in `BucketSpannerMeta`. -/
def BucketSpannerMeta.set {L cap : ℕ} (x : BucketSpannerMeta L cap) (j : Fin cap)
    (val : Option (ℕ × DSHist × DynSpannerMeta L)) : BucketSpannerMeta L cap :=
  ⟨Function.update x.slots j val⟩

/-- Footprint of `bucketSpannerDS`: the `cap`-word handle table `[tbl, tbl + cap)` together with
the `metaFoot` of every active slot. -/
def bucketFoot {L cap : ℕ} (tbl : ℕ) (x : BucketSpannerMeta L cap) (a : ℕ) : Prop :=
  (tbl ≤ a ∧ a < tbl + cap) ∨
  ∃ j : Fin cap, ∃ b m, x.slots j = some (b, m) ∧ metaFoot b m.2 a

/-- Representation invariant for `bucketSpannerDS`: each slot matches its handle table entry and
the representation `dynSpannerRep` (disjoint from `[tbl, tbl + cap)`), and distinct active slots
have disjoint footprints. -/
def BucketSpannerRepAt (P : DSParams) (cap tbl : ℕ) (S : BucketSpannerState cap)
    (x : BucketSpannerMeta P.L cap) (mem : ℕ → ℕ) : Prop :=
  (∀ j : Fin cap,
    match S j, x.slots j with
    | none, none => mem (tbl + j.1) = 0
    | some s, some (b, m) =>
        mem (tbl + j.1) = b ∧
        (dynSpannerRep P).rep b s m mem ∧
        ∀ a, metaFoot b m.2 a → a < tbl ∨ tbl + cap ≤ a
    | _, _ => False) ∧
  (∀ j₁ j₂ : Fin cap, j₁ ≠ j₂ → ∀ b₁ m₁ b₂ m₂,
    x.slots j₁ = some (b₁, m₁) → x.slots j₂ = some (b₂, m₂) →
    ∀ a, metaFoot b₁ m₁.2 a → ¬ metaFoot b₂ m₂.2 a)

/-- The potential of one slot: the bank `DSHist.bank` of its history, or `0` if it is empty. -/
noncomputable def bucketSlotBank (P : DSParams) : Option (ℕ × DSHist × DynSpannerMeta P.L) → ℕ
  | none => 0
  | some (_, m) => m.1.bank P

/-- The potential of `bucketSpannerDS`: the sum of the banks of the slots. -/
noncomputable def bucketPhi (P : DSParams) {cap : ℕ} (x : BucketSpannerMeta P.L cap) : ℕ :=
  ∑ j, bucketSlotBank P (x.slots j)

/-- Changing slot `j` to `v` changes the potential by the bank of `v` minus the old bank. -/
theorem bucketPhi_set (P : DSParams) {cap : ℕ} (x : BucketSpannerMeta P.L cap) (j : Fin cap)
    (v : Option (ℕ × DSHist × DynSpannerMeta P.L)) :
    bucketPhi P (x.set j v) + bucketSlotBank P (x.slots j) =
      bucketPhi P x + bucketSlotBank P v := by
  unfold bucketPhi BucketSpannerMeta.set
  have h1 := Finset.add_sum_erase Finset.univ
    (fun i => bucketSlotBank P (Function.update x.slots j v i)) (Finset.mem_univ j)
  have h2 := Finset.add_sum_erase Finset.univ (fun i => bucketSlotBank P (x.slots i))
    (Finset.mem_univ j)
  have h3 : ∑ i ∈ Finset.univ.erase j, bucketSlotBank P (Function.update x.slots j v i) =
      ∑ i ∈ Finset.univ.erase j, bucketSlotBank P (x.slots i) :=
    Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  simp only [Function.update_self] at h1
  simp only at h2 ⊢
  omega

/-- `DSRep` for `bucketSpannerDS P cap`. The potential is the sum of the banks of the slots
(`bucketPhi`), since the updates of `dynSpannerDS` have amortized costs. -/
noncomputable def bucketSpannerRep (P : DSParams) (cap : ℕ) : DSRep (BucketSpannerState cap) where
  τ := BucketSpannerMeta P.L cap
  rep tbl S x mem := BucketSpannerRepAt P cap tbl S x mem
  phi _ x _ := bucketPhi P x
  foot tbl x := bucketFoot tbl x

end

end MinCostFlow.SparseCore.Program
