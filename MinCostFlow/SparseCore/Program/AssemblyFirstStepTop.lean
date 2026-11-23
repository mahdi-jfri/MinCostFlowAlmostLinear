module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue8
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepDriver
public import MinCostFlow.SparseCore.Program.AssemblyBranchStepIface
public import MinCostFlow.SparseCore.Program.AssemblyCodeCarry

import Mathlib.Tactic

/-!
# The top proof of the first step (`AssemblyFirstStepTop`)

The first step of a branch is the procedure `asmFirstStepDriverStmt fMain fMain`, which calls
`asmFirstStepMainStmt fScan fNewAct fP3 fP4`: Phase 1 (the scan), Phase 2 (the new components),
Phase 3 (the bundle table and the tour), Phase 4 (the spanners and the output batch). This file
proves `AsmBrCoreStepAt` for it, `asmFirstStep_coreStepAt_of`, from the run of Phase 1
(`asmFirstStep_phase1_runs`) and from hypotheses for the other phases.

The hypotheses pass the state from one phase to the next through three predicates `Q₂`, `Q₃`,
`Q₄`, which the later proofs choose (the posts of `asmFirstNewAct_runs`, `asmFirstPhase3_runs`
and `asmFirstPhase4_runs_of_sel`, with what the post of the step needs):
* the packaging: `hf`, `hfMain`, `hfScan`, `hfNewAct`, `hfP3`, `hfP4`, the procedures at
  their indices;
* the space: `space`, `space_mono`, `spaceP`, `space_le`, and `hSp1`, the room of Phase 1;
* the glue of Phase 2 (`hP2`), of Phase 3 (`hP3`) and of Phase 4 (`hP4`): each runs its phase on
  the arguments that the driver passes, from the state that the phase before leaves;
* the post with the cost (`hPost`): from the state after Phase 4, the post of `AsmBrCoreStepAt`
  for the final memory, which is the memory after Phase 4 with the place of the split lists at
  `h + 1`, and for every cost up to the sum of the four costs and `340`.
The premises and the post of one call are `AsmFsPreRaw` and `AsmFsPostRaw`, copied from
`AsmBrCoreStepAt.runs`, and `AsmFsArgs` holds the arguments of the call.

`AsmFsPieces` bundles the hypotheses into one proposition, with the indices, the bodies, the space
function and `Q₂`, `Q₃`, `Q₄` chosen inside it. From it, `asmFirstStep_coreStepAt_exists` gives
`AsmBrCoreStepAt` with the chosen multipliers and space polynomial, and `asmFirstStep_scProg_of`
puts this in the form of the hypothesis `hFirstStep` of the dry run
(`Final/AssemblyDryRunSCTermCode.lean`), on `scProg` with the
constants `C : ScFirstConsts`. Only `asmFirstStep_scProg_of` is used later.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

@[expose] public section

/-- **The premises of one call of the first step**, as `AsmBrCoreStepAt.runs` states them, for
the space function `space`. The bound `depth ≤ Expander.chosenL ((M + N) ^ 2)` of the call comes
last. -/
def AsmFsPreRaw {depth : ℕ} (TR : ℕ → ℕ → DSRep AsmTourAbs)
    (B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState))
    (impl : SparsifyImpl) (P L capExp limbMul wordExp w : ℕ) (Ψ : BundleTreeState depth → ℕ)
    (space : ℕ → ℕ)
    (b batch words edits editWords chg spPtr h k M N n : ℕ) (tr : BundleTreeState depth)
    (ord : ℕ → List End) (x : (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ)
    (U : List Update) (ed : List OrdEdit) (c : LSFChange) (mem : ℕ → ℕ) : Prop :=
  let R := asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ
  let ord' := applyOrdEdits ord ed
  let sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut :=
    fun _ => canonicalSparsify impl
  let info := stepBundleTree sparsify tr U ord ord'
  tr.m₀ = M ∧
  tr.n₀ = N ∧
  1 ≤ depth ∧
  depth ≤ bundleLogFactor M N ∧
  16 ≤ 2 ^ w ∧
  (M + N + 2) ^ wordExp * (L + 1) < 2 ^ w ∧
  ((n + U.length : ℕ) : ℝ) ≤ SparseCoreTool.updateThreshold k M N ∧
  BranchUpdatesBelow impl tr n ∧
  BranchUpdatesBelow impl info.state (n + U.length) ∧
  R.rep b ⟨tr, ord, x.vCap, x.eCap⟩ x mem ∧
  AsmBrModelFacts impl x.vCap x.eCap info.state ord' ∧
  SmallBatchAt mem batch tr.cs.G U words ∧
  tr.cs.G.BatchIsValid U ∧
  BatchWithinCaps x.vCap x.eCap U ∧
  OrdEditsAt mem edits ed editWords ∧
  OrderedBatch tr.cs.G U ord ord' ∧
  OrdEditsValidFor x.vCap x.eCap ord ed ∧
  OrdEditsForBatch tr.cs.G U ed ∧
  LSFChangeAt mem chg c ∧
  c.Exact tr.cs.lsf (compLSFBatch tr.cs U).lsf ∧
  SplitEntriesAt mem spPtr (canonSplitList tr.cs U) ∧
  InputAt w mem (R.foot b x) batch words h ∧
  InputAt w mem (R.foot b x) edits editWords h ∧
  InputAt w mem (R.foot b x) chg c.words h ∧
  InputAt w mem (R.foot b x) spPtr (splitEntriesWords (canonSplitList tr.cs U)) h ∧
  (∀ a, R.foot b x a → a < h) ∧
  (∀ a ∈ [b, batch, words, edits, editWords, chg, spPtr, h], a < 2 ^ w) ∧
  ZeroFrom mem h ∧
  h + space (M + N + k + x.vCap + x.eCap + L + depth + words + editWords) < 2 ^ w ∧
  depth ≤ Expander.chosenL ((M + N) ^ 2)

/-- **The post of one call of the first step**, as `AsmBrCoreStepAt.runs` states it, for the return
value `ov`, the final memory `mem'` and the cost `cost`. -/
def AsmFsPostRaw {depth : ℕ} (TR : ℕ → ℕ → DSRep AsmTourAbs)
    (B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState))
    (impl : SparsifyImpl) (P L capExp limbMul w : ℕ) (Ψ : BundleTreeState depth → ℕ)
    (mul ysMul : ℕ) (space : ℕ → ℕ)
    (b _batch words _edits editWords _chg _spPtr h k M N _n : ℕ) (tr : BundleTreeState depth)
    (ord : ℕ → List End) (x : (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ)
    (U : List Update) (ed : List OrdEdit) (_c : LSFChange) (mem : ℕ → ℕ) (ov : ℕ) (mem' : ℕ → ℕ)
    (cost : ℕ) : Prop :=
  let R := asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ
  let ord' := applyOrdEdits ord ed
  let sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut :=
    fun _ => canonicalSparsify impl
  let info := stepBundleTree sparsify tr U ord ord'
  ∃ yEmb sTour xTour xRest Ys T₀,
    let x₁ := x.afterCore yEmb sTour xTour xRest
    let avoid : ℕ → Prop := fun a =>
      (outGraphRep x.vCap x.eCap).foot x.outH x.gOut a ∨
        (TR x.vCap x.eCap).foot x.tourH xTour a
    (embRep x.eCap).rep x.embH yEmb.view yEmb mem' ∧
    (coreGraph info.state.cs.G info.state.cs.lsf).E ⊆ yEmb.view.dom ∧
    (∀ e ∈ (coreGraph info.state.cs.G info.state.cs.lsf).E,
      yEmb.view.emb e = info.state.emb e) ∧
    (asmBrTourView TR ⟨info.state, ord', x.vCap, x.eCap⟩ x.vCap x.eCap).rep x.tourH sTour xTour
      mem' ∧
    (∃ E₀ : Finset ℕ, outKeep sparsify tr U ord ord' ⊆ E₀ ∧ E₀ ⊆ tr.S_cur.E ∧
      OutMarksOf sTour (outCoreOrder info.state ord') E₀) ∧
    (asmBrSideRep B5 impl w depth L capExp limbMul Ψ).rep x.restH
      ⟨info.state, ord', x.vCap, x.eCap⟩ xRest mem' ∧
    xRest.slotCap = x.xRest.slotCap ∧ xRest.vCap5 = x.vCap ∧ xRest.eCap5 = x.eCap ∧
    AsmBrDisjoint (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) b x₁ ∧
    (∀ a, (asmBrPart (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) b x 0 a ∨
      asmBrPart (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) b x 1 a ∨
      asmBrPart (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) b x 3 a) →
      mem' a = mem a) ∧
    OutStepInAt mem' (mem' (h + ASM_ST_DEL)) (mem' (h + ASM_ST_SPLIT))
      (mem' (h + ASM_ST_INS)) ov avoid sparsify tr U ord ord' Ys ∧
    mem' (mem' (h + ASM_ST_ROT)) = T₀.length ∧
    ListAt mem' (mem' (h + ASM_ST_ROT) + 1) T₀ ∧
    OutCellsFree (mem' (h + ASM_ST_ROT)) (1 + T₀.length) ov avoid ∧
    T₀.Nodup ∧ (∀ v ∈ T₀, v < x.vCap) ∧ OutRotCover sparsify tr U ord ord' T₀ ∧
    readList mem' (mem' (h + ASM_ST_REEMB)) (mem' (h + ASM_ST_REEMBLEN)) =
      stepBundleTree_reembList sparsify tr U ord ord' ∧
    h + ASM_ST_SIZE ≤ mem' (h + ASM_ST_REEMB) ∧
    OutCellsFree (mem' (h + ASM_ST_REEMB)) (mem' (h + ASM_ST_REEMBLEN)) ov avoid ∧
    (∀ i < ASM_ST_SIZE, mem' (h + i) < 2 ^ w) ∧
    (Ys.map List.length).sum + T₀.length ≤
      ysMul * (tr.S_cur.batchEnc info.U_S + words + editWords + 1) *
        (Nat.log 2 (M + N + 2) + 1) ∧
    h + ASM_ST_SIZE ≤ ov ∧
    ov ≤ h + space (M + N + k + x.vCap + x.eCap + L + depth + words + editWords) ∧
    ZeroFrom mem' ov ∧
    (∀ a < h, ¬ R.foot b x a → mem' a = mem a) ∧
    (∀ a, R.foot b x₁ a → R.foot b x a ∨ (h + ASM_ST_SIZE ≤ a ∧ a < ov)) ∧
    cost + R.phi b x₁ mem' ≤
      mul * (branchStepCharge sparsify tr U ord ord' +
        (words + editWords + 1) * bundleLogFactor M N) + R.phi b x mem

/-- **The arguments of one call of the first step**, with the branch state of type `τ`. -/
structure AsmFsArgs (τ : Type) (depth : ℕ) where
  b : ℕ
  batch : ℕ
  words : ℕ
  edits : ℕ
  editWords : ℕ
  chg : ℕ
  spPtr : ℕ
  h : ℕ
  k : ℕ
  M : ℕ
  N : ℕ
  n : ℕ
  tr : BundleTreeState depth
  ord : ℕ → List End
  x : τ
  U : List Update
  ed : List OrdEdit
  c : LSFChange
  mem : ℕ → ℕ
  pos : ℕ
  ω : ℕ → Bool

/-- `AsmFsPreRaw` on the arguments `A`. -/
def AsmFsPre {depth : ℕ} (TR : ℕ → ℕ → DSRep AsmTourAbs)
    (B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState))
    (impl : SparsifyImpl) (P L capExp limbMul wordExp w : ℕ) (Ψ : BundleTreeState depth → ℕ)
    (space : ℕ → ℕ)
    (A : AsmFsArgs (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ
      depth) : Prop :=
  AsmFsPreRaw TR B5 impl P L capExp limbMul wordExp w Ψ space A.b A.batch A.words A.edits
    A.editWords A.chg A.spPtr A.h A.k A.M A.N A.n A.tr A.ord A.x A.U A.ed A.c A.mem

/-- `AsmFsPostRaw` on the arguments `A`. -/
def AsmFsPost {depth : ℕ} (TR : ℕ → ℕ → DSRep AsmTourAbs)
    (B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState))
    (impl : SparsifyImpl) (P L capExp limbMul w : ℕ) (Ψ : BundleTreeState depth → ℕ)
    (mul ysMul : ℕ) (space : ℕ → ℕ)
    (A : AsmFsArgs (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ depth)
    (ov : ℕ) (mem' : ℕ → ℕ) (cost : ℕ) : Prop :=
  AsmFsPostRaw TR B5 impl P L capExp limbMul w Ψ mul ysMul space A.b A.batch A.words A.edits
    A.editWords A.chg A.spPtr A.h A.k A.M A.N A.n A.tr A.ord A.x A.U A.ed A.c A.mem ov mem' cost

end

public section

set_option maxHeartbeats 1600000 in
/-- **The first step meets `AsmBrCoreStepAt`**, from the run of Phase 1 and the hypotheses of the
module docstring: the packaging, the space, the glue of Phases 2, 3 and 4, and the post with the
cost. The main procedure runs the four phases (`asmFirstStepMain_run_of`), and the driver calls it
whether the edge cap is `0` or not (`asmFirstStepDriver_run_self`). The cells that the main
procedure reads come from the rep (`asmFirstStep_cells_of_rep`), and its words fit below `h`
(`asmFirstStep_bounds_of_foot`). -/
noncomputable def asmFirstStep_coreStepAt_of {depth : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ}
    {p : Program} {f fMain fScan fNewAct fP3 fP4 : ℕ} {bNewAct bP3 bP4 : Stmt}
    (hf : p.procs[f]? = some (asmFirstStepDriverStmt fMain fMain))
    (hfMain : p.procs[fMain]? = some (asmFirstStepMainStmt fScan fNewAct fP3 fP4))
    (hfScan : p.procs[fScan]? = some asmFirstScanBatchStmt)
    (hfNewAct : p.procs[fNewAct]? = some bNewAct) (hfP3 : p.procs[fP3]? = some bP3)
    (hfP4 : p.procs[fP4]? = some bP4)
    (mul ysMul : ℕ) (space : ℕ → ℕ) (space_mono : Monotone space) (spaceP : PolyBound)
    (space_le : ∀ s, space s ≤ spaceP.eval s)
    (Q₂ : AsmFsArgs (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ
      depth → State → ℕ → Outcome → State → ℕ → Prop)
    (Q₃ : AsmFsArgs (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ
      depth → State → ℕ → Outcome → State → ℕ → Outcome → State → ℕ →
      Prop)
    (Q₄ : AsmFsArgs (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ
      depth → State → ℕ → Outcome → State → ℕ → Outcome → State → ℕ →
      Outcome → State → ℕ → Prop)
    (hSp1 : ∀ A, AsmFsPre TR B5 impl P L capExp limbMul wordExp w Ψ space A →
      A.h + 6 + asmFirstScanBatchSpace A.x.vCap A.x.eCap A.words < 2 ^ w)
    (hP2 : ∀ A (st₁ : State) (c₁ : ℕ), AsmFsPre TR B5 impl P L capExp limbMul wordExp w Ψ space A →
      ScanMemAt A.mem st₁.mem A.x.xRest.cmpH A.x.xRest.ctH A.x.xRest.comps.length A.x.vCap
        A.x.eCap A.words (A.h + 6) (scanBatchFold A.tr.cs.G
        (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps
        A.tr.activeComps) A.U) →
      st₁.mem (A.h + 6) = (scanBatchFold A.tr.cs.G
        (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps
        A.tr.activeComps) A.U).newComps.length →
      st₁.mem (A.h + 7) = (scanBatchFold A.tr.cs.G
        (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps
        A.tr.activeComps) A.U).delEdges.length →
      c₁ ≤ 245 * A.words + 120 →
      ∃ o₂ st₂ c₂, Runs w p A.ω bNewAct (startState [A.x.restH, A.x.tourH,
          A.h + 9 + 2 * A.x.eCap + A.x.vCap, st₁.mem (A.h + 6),
          A.h + 6 + asmFirstScanBatchSpace A.x.vCap A.x.eCap A.words] st₁.mem st₁.pos) o₂ st₂ c₂ ∧
        Q₂ A st₁ c₁ o₂ st₂ c₂)
    (hP3 : ∀ A st₁ c₁ o₂ st₂ c₂, AsmFsPre TR B5 impl P L capExp limbMul wordExp w Ψ space A →
      Q₂ A st₁ c₁ o₂ st₂ c₂ →
      ∃ o₃ st₃ c₃, Runs w p A.ω bP3 (startState [A.x.xRest.bunH, A.x.xRest.slotCap, A.x.vCap,
          A.x.tourH, A.batch, A.words, A.edits, A.editWords, A.spPtr,
          A.h + 9 + 2 * A.x.eCap + A.x.vCap + 4 * A.words, st₁.mem (A.h + 7), o₂.value]
          st₂.mem st₂.pos) o₃ st₃ c₃ ∧
        o₂.value + 1 < 2 ^ w ∧ st₃.mem (o₂.value + 1) + 1 < 2 ^ w ∧
        Q₃ A st₁ c₁ o₂ st₂ c₂ o₃ st₃ c₃)
    (hP4 : ∀ A st₁ c₁ o₂ st₂ c₂ o₃ st₃ c₃,
      AsmFsPre TR B5 impl P L capExp limbMul wordExp w Ψ space A →
      Q₃ A st₁ c₁ o₂ st₂ c₂ o₃ st₃ c₃ →
      ∃ o₄ st₄ c₄, Runs w p A.ω bP4 (startState [A.x.xRest.spanH, st₃.mem (o₂.value + 1) + 1,
          st₃.mem (st₃.mem (o₂.value + 1)), o₃.value, A.x.eCap, A.x.gOut + 4 + 7 * A.x.vCap,
          A.x.embH, A.x.xRest.slots.length, st₂.mem (A.x.restH + 3), A.batch, A.chg,
          A.h + 6 + asmFirstScanBatchSpace A.x.vCap A.x.eCap A.words, st₁.mem (A.h + 6),
          A.x.tourH, A.spPtr, A.edits, A.h] st₃.mem st₃.pos) o₄ st₄ c₄ ∧
        Q₄ A st₁ c₁ o₂ st₂ c₂ o₃ st₃ c₃ o₄ st₄ c₄)
    (hPost : ∀ A st₁ c₁ o₂ st₂ c₂ o₃ st₃ c₃ o₄ st₄ c₄,
      AsmFsPre TR B5 impl P L capExp limbMul wordExp w Ψ space A →
      Q₄ A st₁ c₁ o₂ st₂ c₂ o₃ st₃ c₃ o₄ st₄ c₄ →
      ∀ mem', mem' = Function.update st₄.mem (A.h + 1) (st₃.mem o₂.value) →
      ∀ cost, cost ≤ c₁ + c₂ + c₃ + c₄ + 340 →
      AsmFsPost TR B5 impl P L capExp limbMul w Ψ mul ysMul space A o₄.value mem' cost) :
    AsmBrCoreStepAt TR B5 impl depth P L capExp limbMul wordExp w Ψ p f := by
  refine ⟨mul, ysMul, space, space_mono, spaceP, space_le, ?_⟩
  intro b batch words edits editWords chg spPtr h k M N n tr ord x U ed c mem pos ω R ord'
    sparsify info hM hN hd1 hdL hdC hw16 hW hthr hUB hUB' hR hFacts hBat hU hCaps hEd hOB hOVF hOFB
    hChg hcEx hSpE hBin hEin hCin hSin hfoot hwords hz hspace
  have hA : AsmFsPre TR B5 impl P L capExp limbMul wordExp w Ψ space
      (⟨b, batch, words, edits, editWords, chg, spPtr, h, k, M, N, n, tr, ord, x, U, ed, c, mem,
        pos, ω⟩ : AsmFsArgs (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ
          depth) := by
    unfold AsmFsPre AsmFsPreRaw
    exact ⟨hM, hN, hd1, hdL, hw16, hW, hthr, hUB, hUB', hR, hFacts, hBat, hU, hCaps, hEd, hOB,
      hOVF, hOFB, hChg, hcEx, hSpE, hBin, hEin, hCin, hSin, hfoot, hwords, hz, hspace, hdC⟩
  obtain ⟨hm_rest, hm_tour, hm_v, hm_e, hm_rd, hm_emb, hm_out, hm_g, -, hm_og, -, hm_bun,
    hm_span, hm_lo, hm_sc, hm_cmp, hm_ct⟩ := asmFirstStep_cells_of_rep hR
  obtain ⟨hbB, hbRd, hbS, hbG⟩ := asmFirstStep_bounds_of_foot hfoot
  have hh_lt : h < 2 ^ w := hwords h (by simp)
  have hsp1 : h + 6 + asmFirstScanBatchSpace x.vCap x.eCap words < 2 ^ w := hSp1 _ hA
  obtain ⟨st₁, c₁, hr₁, h6, h7, hM1, hc₁⟩ := asmFirstStep_phase1_runs (p := p) (ω := ω)
    (pos := pos) hR hU hCaps hBat.1 hBin hfoot hw16 hz hsp1
  obtain ⟨o₂, st₂, c₂, hr₂, hQ₂⟩ := hP2 _ st₁ c₁ hA hM1 h6 h7 hc₁
  obtain ⟨o₃, st₃, c₃, hr₃, ho₂w, hdw, hQ₃⟩ := hP3 _ st₁ c₁ o₂ st₂ c₂ hA hQ₂
  obtain ⟨o₄, st₄, c₄, hr₄, hQ₄⟩ := hP4 _ st₁ c₁ o₂ st₂ c₂ o₃ st₃ c₃ hA hQ₃
  have hASM : ASM_BR_SIZE = 16 := rfl
  have hRF : readFullWords = 11 := rfl
  have hSD : ASM_SD_SIZE = 16 := rfl
  obtain ⟨stM, cM, hrM, hmemM, hcM⟩ := asmFirstStepMain_run_of hfScan hfNewAct hfP3 hfP4
    hm_rest hm_tour hm_v hm_e hm_rd hm_g hm_cmp hm_ct hm_lo hm_bun hm_sc hm_span hm_emb hm_out
    hm_og hw16 (by omega) (by omega) (by omega) (by unfold dynGraphSize at hbG; omega)
    (by unfold asmFirstScanBatchSpace at hsp1; omega) hr₁ rfl rfl hr₂ rfl hr₃ rfl rfl rfl ho₂w
    hdw hr₄
  obtain ⟨stD, cD, hrD, hmemD, hcD⟩ := asmFirstStepDriver_run_self hfMain hw16 (by omega) hrM
  refine ⟨_, hf, .returned o₄.value, stD, cD, ?_⟩
  obtain ⟨yEmb, sTour, xTour, xRest, Ys, T₀, hp⟩ := hPost _ st₁ c₁ o₂ st₂ c₂ o₃ st₃ c₃ o₄ st₄ c₄
    hA hQ₄ stD.mem (hmemD.trans hmemM) cD (by omega)
  exact ⟨yEmb, sTour, xTour, xRest, Ys, T₀, hrD, hp⟩

end

@[expose] public section

/-- **The pieces of the first step**, for the multipliers `mul` and `ysMul`
and the space polynomial `spaceP`: the hypotheses of `asmFirstStep_coreStepAt_of`, with the
indices of the procedures, their bodies, the space function and the predicates `Q₂`, `Q₃`, `Q₄`
chosen by the prover. -/
def AsmFsPieces {depth : ℕ} (TR : ℕ → ℕ → DSRep AsmTourAbs)
    (B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState))
    (impl : SparsifyImpl) (P L capExp limbMul wordExp w : ℕ) (Ψ : BundleTreeState depth → ℕ)
    (p : Program) (f : ℕ) (mul ysMul : ℕ) (spaceP : PolyBound) : Prop :=
  ∃ (fMain fScan fNewAct fP3 fP4 : ℕ) (bNewAct bP3 bP4 : Stmt) (space : ℕ → ℕ)
    (Q₂ : AsmFsArgs (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ
        depth → State → ℕ → Outcome → State → ℕ → Prop)
    (Q₃ : AsmFsArgs (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ
        depth → State → ℕ → Outcome → State → ℕ → Outcome → State → ℕ →
        Prop)
    (Q₄ : AsmFsArgs (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ
        depth → State → ℕ → Outcome → State → ℕ → Outcome → State → ℕ →
        Outcome → State → ℕ → Prop),
    (p.procs[f]? = some (asmFirstStepDriverStmt fMain fMain)) ∧
    (p.procs[fMain]? = some (asmFirstStepMainStmt fScan fNewAct fP3 fP4)) ∧
    (p.procs[fScan]? = some asmFirstScanBatchStmt) ∧
    (p.procs[fNewAct]? = some bNewAct) ∧
    (p.procs[fP3]? = some bP3) ∧
    (p.procs[fP4]? = some bP4) ∧
    (Monotone space) ∧
    (∀ s, space s ≤ spaceP.eval s) ∧
    (∀ A, AsmFsPre TR B5 impl P L capExp limbMul wordExp w Ψ space A →
        A.h + 6 + asmFirstScanBatchSpace A.x.vCap A.x.eCap A.words < 2 ^ w) ∧
    (∀ A (st₁ : State) (c₁ : ℕ), AsmFsPre TR B5 impl P L capExp limbMul wordExp w Ψ space A →
        ScanMemAt A.mem st₁.mem A.x.xRest.cmpH A.x.xRest.ctH A.x.xRest.comps.length A.x.vCap
          A.x.eCap A.words (A.h + 6) (scanBatchFold A.tr.cs.G
          (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps
          A.tr.activeComps) A.U) →
        st₁.mem (A.h + 6) = (scanBatchFold A.tr.cs.G
          (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps
          A.tr.activeComps) A.U).newComps.length →
        st₁.mem (A.h + 7) = (scanBatchFold A.tr.cs.G
          (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps
          A.tr.activeComps) A.U).delEdges.length →
        c₁ ≤ 245 * A.words + 120 →
        ∃ o₂ st₂ c₂, Runs w p A.ω bNewAct (startState [A.x.restH, A.x.tourH,
            A.h + 9 + 2 * A.x.eCap + A.x.vCap, st₁.mem (A.h + 6),
            A.h + 6 + asmFirstScanBatchSpace A.x.vCap A.x.eCap A.words] st₁.mem st₁.pos) o₂ st₂ c₂ ∧
          Q₂ A st₁ c₁ o₂ st₂ c₂) ∧
    (∀ A st₁ c₁ o₂ st₂ c₂, AsmFsPre TR B5 impl P L capExp limbMul wordExp w Ψ space A →
        Q₂ A st₁ c₁ o₂ st₂ c₂ →
        ∃ o₃ st₃ c₃, Runs w p A.ω bP3 (startState [A.x.xRest.bunH, A.x.xRest.slotCap, A.x.vCap,
            A.x.tourH, A.batch, A.words, A.edits, A.editWords, A.spPtr,
            A.h + 9 + 2 * A.x.eCap + A.x.vCap + 4 * A.words, st₁.mem (A.h + 7), o₂.value]
            st₂.mem st₂.pos) o₃ st₃ c₃ ∧
          o₂.value + 1 < 2 ^ w ∧ st₃.mem (o₂.value + 1) + 1 < 2 ^ w ∧
          Q₃ A st₁ c₁ o₂ st₂ c₂ o₃ st₃ c₃) ∧
    (∀ A st₁ c₁ o₂ st₂ c₂ o₃ st₃ c₃,
        AsmFsPre TR B5 impl P L capExp limbMul wordExp w Ψ space A →
        Q₃ A st₁ c₁ o₂ st₂ c₂ o₃ st₃ c₃ →
        ∃ o₄ st₄ c₄, Runs w p A.ω bP4 (startState [A.x.xRest.spanH, st₃.mem (o₂.value + 1) + 1,
            st₃.mem (st₃.mem (o₂.value + 1)), o₃.value, A.x.eCap, A.x.gOut + 4 + 7 * A.x.vCap,
            A.x.embH, A.x.xRest.slots.length, st₂.mem (A.x.restH + 3), A.batch, A.chg,
            A.h + 6 + asmFirstScanBatchSpace A.x.vCap A.x.eCap A.words, st₁.mem (A.h + 6),
            A.x.tourH, A.spPtr, A.edits, A.h] st₃.mem st₃.pos) o₄ st₄ c₄ ∧
          Q₄ A st₁ c₁ o₂ st₂ c₂ o₃ st₃ c₃ o₄ st₄ c₄) ∧
    (∀ A st₁ c₁ o₂ st₂ c₂ o₃ st₃ c₃ o₄ st₄ c₄,
        AsmFsPre TR B5 impl P L capExp limbMul wordExp w Ψ space A →
        Q₄ A st₁ c₁ o₂ st₂ c₂ o₃ st₃ c₃ o₄ st₄ c₄ →
        ∀ mem', mem' = Function.update st₄.mem (A.h + 1) (st₃.mem o₂.value) →
        ∀ cost, cost ≤ c₁ + c₂ + c₃ + c₄ + 340 →
        AsmFsPost TR B5 impl P L capExp limbMul w Ψ mul ysMul space A o₄.value mem' cost)

end

public section

/-- **The pieces give `AsmBrCoreStepAt`** with the multipliers `mul` and `ysMul` and the space
polynomial `spaceP` (`asmFirstStep_coreStepAt_of`). -/
theorem asmFirstStep_coreStepAt_exists {depth : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ}
    {p : Program} {f mul ysMul : ℕ} {spaceP : PolyBound}
    (h : AsmFsPieces TR B5 impl P L capExp limbMul wordExp w Ψ p f mul ysMul spaceP) :
    ∃ JS : AsmBrCoreStepAt TR B5 impl depth P L capExp limbMul wordExp w Ψ p f,
      JS.mul = mul ∧ JS.ysMul = ysMul ∧ JS.spaceP = spaceP := by
  obtain ⟨fMain, fScan, fNewAct, fP3, fP4, bNewAct, bP3, bP4, space, Q₂, Q₃, Q₄, hf, hfMain,
    hfScan, hfNewAct, hfP3, hfP4, hmono, hle, hSp1, hP2, hP3, hP4, hPost⟩ := h
  exact ⟨asmFirstStep_coreStepAt_of hf hfMain hfScan hfNewAct hfP3 hfP4 mul ysMul space hmono
    spaceP hle Q₂ Q₃ Q₄ hSp1 hP2 hP3 hP4 hPost, rfl, rfl, rfl⟩

/-- **The first step on `scProg`, with the constants `C`**, in the form of the hypothesis
`hFirstStep` of the dry run (`Final/AssemblyDryRunSCTermCode.lean`): for every depth `1 ≤ depth`,
every P4 family `CF` and `P ≤ 4 L_in`, the procedure `fCoreS` of the layout meets
`AsmBrCoreStepAt` with the multipliers `C.stepMul` and `C.stepYs` and the space `C.stepSpace`,
from the pieces at the same parameters (`asmFirstStep_coreStepAt_exists`). The word exponent is
`asmBrWordExp C.toAsmBrConsts capExp`. The bound `C.firstWordExp 3 ≤ 39` of the dry run is for
the init, and the step does not use it. -/
theorem asmFirstStep_scProg_of {CFS : AsmCompFamilySpec} {lsfInit : ℕ → ℕ → LSFInit}
    {impl : SparsifyImpl} {cf : ScCompCode} {firstStep firstInit : ScSubCode}
    {C : ScFirstConsts}
    (hPieces :
      let L := scLayout impl cf firstStep firstInit
      let p := scProg impl cf firstStep firstInit
      ∀ depth : ℕ, 1 ≤ depth →
        ∀ (capExp limbMul w : ℕ) (fmt : Num.Format w) (L_in : ℕ)
          (_CF : AsmCompFamilyAt CFS (lsfInit L_in fmt.precision) w fmt L_in capExp limbMul
            p cf.fInit cf.fBatch),
          fmt.precision ≤ 4 * L_in →
          AsmFsPieces (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)) scProgB5
            impl fmt.precision L_in capExp limbMul (asmBrWordExp C.toAsmBrConsts capExp) w
            (walkPot (L := depth)) p L.I.fCoreS (C.stepMul capExp limbMul)
            (C.stepYs capExp limbMul) (C.stepSpace capExp)) :
    let L := scLayout impl cf firstStep firstInit
    let p := scProg impl cf firstStep firstInit
    ∀ depth : ℕ, 1 ≤ depth →
      ∀ (capExp limbMul w : ℕ) (fmt : Num.Format w) (L_in : ℕ)
        (CF : AsmCompFamilyAt CFS (lsfInit L_in fmt.precision) w fmt L_in capExp limbMul
          p cf.fInit cf.fBatch),
        fmt.precision ≤ 4 * L_in → CF.fRoot = cf.fRoot →
        ∃ JS : AsmBrCoreStepAt
            (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)) scProgB5 impl depth
            fmt.precision L_in capExp limbMul (asmBrWordExp C.toAsmBrConsts capExp) w walkPot p
            L.I.fCoreS,
          JS.mul = C.stepMul capExp limbMul ∧
          JS.ysMul = C.stepYs capExp limbMul ∧
          JS.spaceP = C.stepSpace capExp := by
  intro L p depth hd capExp limbMul w fmt L_in CF hP _
  exact asmFirstStep_coreStepAt_exists (hPieces depth hd capExp limbMul w fmt L_in CF hP)

end

end MinCostFlow.SparseCore.Program
