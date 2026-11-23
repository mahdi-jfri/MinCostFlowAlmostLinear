module

public import MinCostFlow.SparseCore.Program.AssemblyBranchFull
public import MinCostFlow.SparseCore.Program.CompSplitListModel
public import MinCostFlow.Expander.Section8Asymptotics

/-!
# The step of a branch: the first phase and the program (`AssemblyBranchStepIface`)

An update of the sparse-core tool steps every branch by `stepBundleTree` (`AsmBranchAt.step_runs`,
`AssemblyTopIface.lean`). On the machine one step of a branch runs in this order:
the tour of P2 applies the order edits and the cuts and links of the forest
changes, with the helper of P7 after each cut; then the bundles of P5 and the bucket spanners of P6
run; then the output step of P7 writes `U_S` and the edits of the output order; then P10 updates
the readout data.

This file splits the step into three calls (`asmBrStepStmt`):
1. **the first phase** (`AsmBrCoreStepAt`): everything before the output step of P7. It leaves the
   tour with the new core lists and the ends of the old output edges that stay marked, the bundle
   side with the new state, and the embedding table with the new walks. It writes the input
   records of P7's step (`OutStepInAt`, the list `T₀`) and the list of re-embedded edges;
2. **the output step of P7** (`sig_outStepSmall_runs`);
3. **the update of the readout data of P10** (`ReadBranchAt.step`).
Then the program copies the four output words of P7 and the two words of the re-embedded list to
the places the clause names.

The first phase runs the tour (P2), the bundles (P5), the bucket spanners (P6), the choice of the
leaving and entering output edges, the list `T₀` and the new walks of the embedding table. It is
stated here as an interface, whose post is what the two later calls and the representation of the
branch need.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The offset, in the six words that the first phase writes at the heap pointer `h`, of each
pointer: the leaving edges, the first split record, the entering edges and the list `T₀` (the
input records of P7's step), then the address and the length of the list of re-embedded edges. -/
def ASM_ST_DEL : ℕ := 0
def ASM_ST_SPLIT : ℕ := 1
def ASM_ST_INS : ℕ := 2
def ASM_ST_ROT : ℕ := 3
def ASM_ST_REEMB : ℕ := 4
def ASM_ST_REEMBLEN : ℕ := 5
/-- The number of words that the first phase writes at the heap pointer. -/
def ASM_ST_SIZE : ℕ := 6

/-- The new concrete state of a branch after the first phase of a step: only the embedding
table, the tour and the bundle side change. -/
def AsmBrConc.afterCore {TR : ℕ → ℕ → DSRep AsmTourAbs} {τX : Type} (x : AsmBrConc TR τX)
    (yEmb : EmbConc) (sTour : OutTourAbs) (xTour : (TR x.vCap x.eCap).τ) (xRest : τX) :
    AsmBrConc TR τX :=
  { x with yEmb := yEmb, sTour := sTour, xTour := xTour, xRest := xRest }

/-- **Interface of the first phase of the step of a branch**, `[b, batch, words, edits, editWords,
chg, h]`, for the branch at `b` in the full representation, the input batch `U`, the order edits
`ed` from `ord` to `ord'`, in one block per update of `U` (`OrdEditsForBatch`), and P4's change
record `c` of the forest at `chg`. Let `info` be
`stepBundleTree` of the branch. The call ends with:
* the embedding table holding `info.state.emb` on the edges of the new core graph;
* P2's tour holding the new order `ord'` and the new forest, so that P7's view of it
  (`asmBrTourView`) holds the new core lists `outCoreOrder info.state ord'`, with the marks of some
  set `E₀` of old output edges between the kept edges `outKeep` and `S_cur.E` (P2 clears the marks
  of an edge that the batch deletes and inserts again);
* the bundle side holding `⟨info.state, ord'⟩`, with the same number of slots and the same caps
  (so P5's invariant `bunRestartInv` holds for the new table and the new core lists);
* the record, the readout data and the output graph unchanged, and the six parts apart;
* at `h` the six words of the input records of P7's step (`OutStepInAt` on the lists `Ys`, the
  list `T₀` with `OutRotCover`) and the list of the re-embedded edges `stepBundleTree_reembList`,
  all outside the cells of the output graph and of the tour (`OutCellsFree`), so that P7's step
  keeps them;
* the size bound `Σ |Y| + |T₀| ≤ ysMul · (Enc(U_S) + words + editWords + 1) · lg`, which pays the
  output step of P7 (the split lists are paid with a log factor, `OutSplitBound.lean`);
* the frame, the growth of the cells of the branch into `[h, o)`, at most `space` new cells (a
  monotone function of the caps and the sizes of the inputs, at most the polynomial `spaceP`), and
  cost at most `mul` times the model's step charge with the input words, against the potential
  of the branch.
The polynomial `spaceP` is a field, so it may depend on all parameters of the interface. The step
clause of `AsmBranchAt` needs it free of `limbMul` (its space `S.stepSpace capExp` does not see
`limbMul`); the value of `AsmBranchAt` (`AssemblyBranchValue.lean`) asks this of the family of
first phases it takes. -/
structure AsmBrCoreStepAt (TR : ℕ → ℕ → DSRep AsmTourAbs)
    (B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState))
    (impl : SparsifyImpl) (depth P L capExp limbMul wordExp w : ℕ) (Ψ : BundleTreeState depth → ℕ)
    (p : Program) (f : ℕ) where
  mul : ℕ
  ysMul : ℕ
  space : ℕ → ℕ
  space_mono : Monotone space
  spaceP : PolyBound
  space_le : ∀ x, space x ≤ spaceP.eval x
  runs : ∀ (b batch words edits editWords chg spPtr h k M N n : ℕ) (tr : BundleTreeState depth)
      (ord : ℕ → List End)
      (x : (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ)
      (U : List Update) (ed : List OrdEdit) (c : LSFChange) (mem : ℕ → ℕ) (pos : ℕ)
      (ω : ℕ → Bool),
      let R := asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ
      let ord' := applyOrdEdits ord ed
      let sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut :=
        fun _ => canonicalSparsify impl
      let info := stepBundleTree sparsify tr U ord ord'
      tr.m₀ = M → tr.n₀ = N →
      1 ≤ depth → depth ≤ bundleLogFactor M N → depth ≤ Expander.chosenL ((M + N) ^ 2) →
      16 ≤ 2 ^ w →
      (M + N + 2) ^ wordExp * (L + 1) < 2 ^ w →
      ((n + U.length : ℕ) : ℝ) ≤ SparseCoreTool.updateThreshold k M N →
      BranchUpdatesBelow impl tr n →
      BranchUpdatesBelow impl info.state (n + U.length) →
      R.rep b ⟨tr, ord, x.vCap, x.eCap⟩ x mem →
      AsmBrModelFacts impl x.vCap x.eCap info.state ord' →
      SmallBatchAt mem batch tr.cs.G U words → tr.cs.G.BatchIsValid U →
      BatchWithinCaps x.vCap x.eCap U →
      OrdEditsAt mem edits ed editWords → OrderedBatch tr.cs.G U ord ord' →
      OrdEditsValidFor x.vCap x.eCap ord ed →
      OrdEditsForBatch tr.cs.G U ed →
      LSFChangeAt mem chg c → c.Exact tr.cs.lsf (compLSFBatch tr.cs U).lsf →
      SplitEntriesAt mem spPtr (canonSplitList tr.cs U) →
      InputAt w mem (R.foot b x) batch words h → InputAt w mem (R.foot b x) edits editWords h →
      InputAt w mem (R.foot b x) chg c.words h →
      InputAt w mem (R.foot b x) spPtr (splitEntriesWords (canonSplitList tr.cs U)) h →
      (∀ a, R.foot b x a → a < h) →
      (∀ a ∈ [b, batch, words, edits, editWords, chg, spPtr, h], a < 2 ^ w) →
      ZeroFrom mem h →
      h + space (M + N + k + x.vCap + x.eCap + L + depth + words + editWords) < 2 ^ w →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' cost yEmb sTour xTour xRest Ys T₀,
        Runs w p ω body (startState [b, batch, words, edits, editWords, chg, spPtr, h] mem pos)
          o st' cost ∧
        let x₁ := x.afterCore yEmb sTour xTour xRest
        let avoid : ℕ → Prop := fun a =>
          (outGraphRep x.vCap x.eCap).foot x.outH x.gOut a ∨
            (TR x.vCap x.eCap).foot x.tourH xTour a
        (embRep x.eCap).rep x.embH yEmb.view yEmb st'.mem ∧
        (coreGraph info.state.cs.G info.state.cs.lsf).E ⊆ yEmb.view.dom ∧
        (∀ e ∈ (coreGraph info.state.cs.G info.state.cs.lsf).E,
          yEmb.view.emb e = info.state.emb e) ∧
        (asmBrTourView TR ⟨info.state, ord', x.vCap, x.eCap⟩ x.vCap x.eCap).rep x.tourH sTour xTour
          st'.mem ∧
        (∃ E₀ : Finset ℕ, outKeep sparsify tr U ord ord' ⊆ E₀ ∧ E₀ ⊆ tr.S_cur.E ∧
          OutMarksOf sTour (outCoreOrder info.state ord') E₀) ∧
        (asmBrSideRep B5 impl w depth L capExp limbMul Ψ).rep x.restH
          ⟨info.state, ord', x.vCap, x.eCap⟩ xRest st'.mem ∧
        xRest.slotCap = x.xRest.slotCap ∧ xRest.vCap5 = x.vCap ∧ xRest.eCap5 = x.eCap ∧
        AsmBrDisjoint (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) b x₁ ∧
        (∀ a, (asmBrPart (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) b x 0 a ∨
          asmBrPart (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) b x 1 a ∨
          asmBrPart (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) b x 3 a) →
          st'.mem a = mem a) ∧
        OutStepInAt st'.mem (st'.mem (h + ASM_ST_DEL)) (st'.mem (h + ASM_ST_SPLIT))
          (st'.mem (h + ASM_ST_INS)) o.value avoid sparsify tr U ord ord' Ys ∧
        st'.mem (st'.mem (h + ASM_ST_ROT)) = T₀.length ∧
        ListAt st'.mem (st'.mem (h + ASM_ST_ROT) + 1) T₀ ∧
        OutCellsFree (st'.mem (h + ASM_ST_ROT)) (1 + T₀.length) o.value avoid ∧
        T₀.Nodup ∧ (∀ v ∈ T₀, v < x.vCap) ∧ OutRotCover sparsify tr U ord ord' T₀ ∧
        readList st'.mem (st'.mem (h + ASM_ST_REEMB)) (st'.mem (h + ASM_ST_REEMBLEN)) =
          stepBundleTree_reembList sparsify tr U ord ord' ∧
        h + ASM_ST_SIZE ≤ st'.mem (h + ASM_ST_REEMB) ∧
        OutCellsFree (st'.mem (h + ASM_ST_REEMB)) (st'.mem (h + ASM_ST_REEMBLEN)) o.value avoid ∧
        (∀ i < ASM_ST_SIZE, st'.mem (h + i) < 2 ^ w) ∧
        (Ys.map List.length).sum + T₀.length ≤
          ysMul * (tr.S_cur.batchEnc info.U_S + words + editWords + 1) *
            (Nat.log 2 (M + N + 2) + 1) ∧
        h + ASM_ST_SIZE ≤ o.value ∧
        o.value ≤ h + space (M + N + k + x.vCap + x.eCap + L + depth + words + editWords) ∧
        ZeroFrom st'.mem o.value ∧
        (∀ a < h, ¬ R.foot b x a → st'.mem a = mem a) ∧
        (∀ a, R.foot b x₁ a → R.foot b x a ∨ (h + ASM_ST_SIZE ≤ a ∧ a < o.value)) ∧
        cost + R.phi b x₁ st'.mem ≤
          mul * (branchStepCharge sparsify tr U ord ord' +
            (words + editWords + 1) * bundleLogFactor M N) + R.phi b x mem

/-! ## The program -/

/-- **The step of a branch**, `[b, cfH, j, batch, words, edits, editWords, fChgPtr, outSlotPtr,
reembSlotPtr, h]` (the arguments of `AsmBranchAt.step_runs`). Registers: `11` P4's change record of
branch `j`, `12`, `13`, `14` the heap pointers after the three calls.
1. read the pointer of the change record of branch `j` from P4's table at `fChgPtr`;
2. call the first phase (`fCore`) on the branch, the batch, the edits, the change record and `h`;
3. call the output step of P7 (`fOut`) on the output graph, the tour, the four input records that
   the first phase wrote at `h`, and the heap pointer;
4. call the update of P10 (`fRead`) on the readout data, the batch, the change record, the output
   batch that P7 wrote, and the heap pointer;
5. copy the four words of P7 to `outSlotPtr` and the two words of the re-embedded list to
   `reembSlotPtr`, and return the heap pointer. -/
def asmBrStepStmt (fCore fOut fRead : ℕ) : Stmt :=
  .assign 12 (.load (.bin .add (.reg 7) (.reg 2))) ;;
  .assign 13 (.load (.bin .add (.reg 11) (.reg 2))) ;;
  .call 14 fCore [.reg 0, .reg 3, .reg 4, .reg 5, .reg 6, .reg 12, .reg 13, .reg 10] ;;
  .call 15 fOut [.load (.bin .add (.reg 0) (.const ASM_BR_OUT)),
    .load (.bin .add (.reg 0) (.const ASM_BR_TOUR)),
    .load (.bin .add (.reg 10) (.const ASM_ST_DEL)),
    .load (.bin .add (.reg 10) (.const ASM_ST_SPLIT)),
    .load (.bin .add (.reg 10) (.const ASM_ST_INS)),
    .load (.bin .add (.reg 10) (.const ASM_ST_ROT)), .reg 14] ;;
  .call 16 fRead [.load (.bin .add (.reg 0) (.const ASM_BR_READ)), .reg 3, .reg 4, .reg 12,
    .load (.reg 14), .load (.bin .add (.reg 14) (.const 1)), .reg 15] ;;
  .store (.reg 8) (.load (.reg 14)) ;;
  .store (.bin .add (.reg 8) (.const 1)) (.load (.bin .add (.reg 14) (.const 1))) ;;
  .store (.bin .add (.reg 8) (.const 2)) (.load (.bin .add (.reg 14) (.const 2))) ;;
  .store (.bin .add (.reg 8) (.const 3)) (.load (.bin .add (.reg 14) (.const 3))) ;;
  .store (.reg 9) (.load (.bin .add (.reg 10) (.const ASM_ST_REEMB))) ;;
  .store (.bin .add (.reg 9) (.const 1)) (.load (.bin .add (.reg 10) (.const ASM_ST_REEMBLEN))) ;;
  .ret (.reg 16)

/-- The step of a branch never reads random bits. -/
theorem asmBrStepStmt_noRand (fCore fOut fRead : ℕ) : (asmBrStepStmt fCore fOut fRead).NoRand := by
  simp [asmBrStepStmt, Stmt.NoRand]

end MinCostFlow.SparseCore.Program
