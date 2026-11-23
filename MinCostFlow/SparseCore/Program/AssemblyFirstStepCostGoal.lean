module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepHP4Defs

import Mathlib.Tactic

/-!
# The cost of the first step, as its own goal (`AssemblyFirstStepCostGoal`)

The top proof of the first step (`asmFirstStep_coreStepAt_of`) asks, as `hPost`, for the post of
`AsmBrCoreStepAt` from the state after Phase 4. That post has two kinds of conjuncts: the facts of
the memory (the new parts of the branch, the records of P7's step, the places and the frame), and
the cost, whose last conjunct says that the cost of the step plus the new potential is at most
`mul` times the charge of the model plus the old potential. This file splits the two, so that they
can be proved apart.

* `AsmFirstPhase4PostAt` and `AsmFsQ₄At`: the post of Phase 4 and the predicate `AsmFsQ₄` after
  Phase 4, with all their witnesses as arguments (`asmFirstPhase4Post_iff`, `asmFsQ₄_at`).
* `asmFsSideAfter`: the bundle side after the step. It is the side `y'` after Phase 2, with the
  bundle table of Phase 3 (`tableAfterStepRuns`), the spanners after the tasks of Phase 4
  (`p4SpanAfter`) and their concrete state `x'`, and the walk potential `Ψ` of the new state.
* `AsmFsPostNCAt` (the post without the cost) and `AsmFsCostAt` (the cost), for given witnesses;
  together they give the post (`asmFsPost_of_nc_cost`).
* `AsmFsCostGoal`: the cost goal. From `AsmFsPre` and `AsmFsQ₄At`, the cost
  `c₁ + c₂ + c₃ + c₄ + 340` of the four phases and the driver meets `AsmFsCostAt` for the branch
  whose tour is the tour of Phase 4 and whose bundle side is `asmFsSideAfter`. The potential of a
  branch does not read the embedding table or the abstract tour (`asmBrPhi`), so the goal holds
  for every `yEmb` and `sTour`.
* `asmFirstStep_hPost_of`: the field `hPost` of `AsmFsPieces` for `Q₄ := AsmFsQ₄`, from the post
  without the cost (for the same tour and bundle side) and the cost goal.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The tour family of `scProg`. -/
local notation "TRc" => asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)

@[expose] public section

/-- **The post of Phase 4 with its witnesses as arguments**: the body of `AsmFirstPhase4Post` for
the task outputs `qs`, the edge lists `ns` of the new slots, the concrete state `x'` of the
spanners, the embedding table `y'`, the tour state `tx'`, the lists `Ld`, `Li`, `Lr` and the
rotation list `T₀`. -/
def AsmFirstPhase4PostAt (P : DSParams) {cap : ℕ} (TR : ℕ → ℕ → DSRep AsmTourAbs)
    (mulE qE mulR qR : ℕ) (spanTbl hp eCap vCap embH lo hi tourH rec : ℕ)
    (S6 : BucketSpannerState cap) (x6 : BucketSpannerMeta P.L cap) (tasks : List SpanUpdTask)
    (v : EmbView) (y : EmbConc) (U : List Update) (ed : List OrdEdit) (c : LSFChange) {nNew : ℕ}
    (lazyE : Fin nNew → List ℕ) (mk : Finset End) (tx₀ : (TR vCap eCap).τ)
    (avoid₀ : ℕ → Prop) (mem₀ : ℕ → ℕ) (tr : BundleTreeState P.L) (ord : ℕ → List End)
    (o : Outcome) (st' : State) (cost : ℕ)
    (qs : List (SpanUpdTask × P4TaskOut)) (ns : List (ℕ × List ℕ))
    (x' : BucketSpannerMeta P.L cap) (y' : EmbConc) (tx' : (TR vCap eCap).τ)
    (Ld Li Lr T₀ : List ℕ) : Prop :=
  let sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify P.impl
  let ord' := applyOrdEdits ord ed
  let cs' := compLSFBatch tr.cs U
  let avoid : ℕ → Prop := fun x => avoid₀ x ∨ (TR vCap eCap).foot tourH tx' x
  qs.map Prod.fst = tasks ∧ (∀ q ∈ qs, P4OutOK P S6 mem₀ q) ∧
  ns.map Prod.fst = List.range' lo (hi - lo) ∧
  (∀ q ∈ ns, ∀ (hs : q.1 < cap) (d : DSHist),
    p4SpanAfter P S6 mem₀ tasks ⟨q.1, hs⟩ = some d →
    q.2.Nodup ∧ q.2.toFinset = (d.state P).G.E) ∧
  (bucketSpannerRep P cap).rep spanTbl (p4SpanAfter P S6 mem₀ tasks) x' st'.mem ∧
  (embRep eCap).rep embH ((p4SpanWV P S6 mem₀ tr.S_cur.E v tasks qs ns).2.apply
    (insSelfChange ((outInsSet sp tr U ord ord').sort (· ≤ ·)))) y' st'.mem ∧
  (TR vCap eCap).rep tourH ⟨ord', cs'.RF, mk⟩ tx' st'.mem ∧
  OutDelAt st'.mem (st'.mem rec) ((outDelSet sp tr U ord ord').sort (· ≤ ·)) cs'.G.E ∧
  OutCellsFree (st'.mem rec) (1 + 2 * (outDelSet sp tr U ord ord').card) o.value avoid ∧
  OutInsAt st'.mem (st'.mem (rec + 2)) ((outInsSet sp tr U ord ord').sort (· ≤ ·))
    (fun e => cs'.RF.root (cs'.G.tail e)) (fun e => cs'.RF.root (cs'.G.head e)) ∧
  OutCellsFree (st'.mem (rec + 2)) (1 + 3 * (outInsSet sp tr U ord ord').card) o.value
    avoid ∧
  st'.mem (st'.mem (rec + 3)) = T₀.length ∧ ListAt st'.mem (st'.mem (rec + 3) + 1) T₀ ∧
  OutCellsFree (st'.mem (rec + 3)) (1 + T₀.length) o.value avoid ∧
  T₀.Nodup ∧ (∀ v ∈ T₀, v < vCap) ∧ OutRotCover sp tr U ord ord' T₀ ∧
  T₀.length ≤ (p4RotRaw (canonSplitList tr.cs U) ((outInsSet sp tr U ord ord').sort (· ≤ ·))
    (fun e => cs'.RF.root (cs'.G.tail e)) (fun e => cs'.RF.root (cs'.G.head e))
    cs'.RF.root U ed).length ∧
  readList st'.mem (st'.mem (rec + 4)) (st'.mem (rec + 5)) =
    stepBundleTree_reembList sp tr U ord ord' ∧
  hp ≤ st'.mem (rec + 4) ∧
  OutCellsFree (st'.mem (rec + 4)) (st'.mem (rec + 5)) o.value avoid ∧
  Ld.length ≤ eCap ∧ Li.length ≤ eCap ∧ Lr.length ≤ eCap ∧
  hp ≤ st'.mem rec ∧ hp ≤ st'.mem (rec + 2) ∧ hp ≤ st'.mem (rec + 3) ∧
  hp ≤ o.value ∧
  o.value ≤ hp + p4WsSize eCap + (tasks.map (p4TaskSpace P S6 mem₀)).sum +
    rangeCost (p4NewSpace P (p4SpanAfter P S6 mem₀ tasks)) lo hi +
    asmFirstPhase4Room vCap eCap (canonSplitList tr.cs U).length U.length ed.length
      qE qR ∧
  ZeroFrom st'.mem o.value ∧
  (∀ a < hp, ¬ bucketFoot spanTbl x6 a → ¬ embFoot eCap embH y a →
    ¬ (TR vCap eCap).foot tourH tx₀ a → (a < rec ∨ rec + 6 ≤ a) → st'.mem a = mem₀ a) ∧
  (∀ a, bucketFoot spanTbl x' a → bucketFoot spanTbl x6 a ∨ (hp ≤ a ∧ a < o.value)) ∧
  (∀ a, embFoot eCap embH y' a → embFoot eCap embH y a ∨ (hp ≤ a ∧ a < o.value)) ∧
  (∀ a, (TR vCap eCap).foot tourH tx' a →
    (TR vCap eCap).foot tourH tx₀ a ∨ (hp ≤ a ∧ a < o.value)) ∧
  (∀ a, embFoot eCap embH y' a → ¬ bucketFoot spanTbl x' a) ∧
  (∀ a, embFoot eCap embH y' a → ¬ (TR vCap eCap).foot tourH tx' a) ∧
  (∀ a, bucketFoot spanTbl x' a → ¬ (TR vCap eCap).foot tourH tx' a) ∧
  cost + specPhi P (p4SpanAfter P S6 mem₀ tasks) + (TR vCap eCap).phi tourH tx' st'.mem ≤
    specPhi P S6 + (tasks.map fun t => p4TaskPay P S6 mem₀ t + 70).sum +
      rangeCost (fun s => p4NewPay P (p4SpanAfter P S6 mem₀ tasks) s + 20) lo hi +
      9 * (hi - lo) + 175 * U.length +
      130 * ((List.finRange nNew).map fun i => (lazyE i).length).sum + 90 * nNew +
      105 * c.fDel.length + 115 * (Ld.length + Li.length) + 620 +
      (2 * (outInsSet sp tr U ord ord').card * (mulE * ordStoreLog eCap + 45) +
        35 * Li.length + outBuildCost Ld.length + outBuildCost Li.length +
        60 * (outInsSet sp tr U ord ord').card + 300) +
      p4RotCost (canonSplitList tr.cs U).length (outInsSet sp tr U ord ord').card U.length
        ed.length (p4RotRaw (canonSplitList tr.cs U)
          ((outInsSet sp tr U ord ord').sort (· ≤ ·))
          (fun e => cs'.RF.root (cs'.G.tail e)) (fun e => cs'.RF.root (cs'.G.head e))
          cs'.RF.root U ed).length vCap (mulR * ordStoreLog eCap + 60) +
      p4ReembCost (Lr.length + (outDelSet sp tr U ord ord').card) + 250 +
      (TR vCap eCap).phi tourH tx₀ mem₀ ∧
  Ld.Nodup ∧ Li.Nodup ∧ Lr.Nodup ∧
  (∀ e, e ∈ Ld ↔ e ∈ (p4SpanWV P S6 mem₀ tr.S_cur.E v tasks qs ns).1.delSup ∨
    e ∈ batchDeletes U) ∧
  (∀ e, e ∈ Li ↔ e ∈ (p4SpanWV P S6 mem₀ tr.S_cur.E v tasks qs ns).1.insSup ∨
    e ∈ batchDeletes U ∨ e ∈ batchInsEdges U ∨ (∃ i : Fin nNew, e ∈ lazyE i) ∨ e ∈ c.fDel) ∧
  (∀ e, e ∈ Lr ↔ e ∈ p4ReembSet P tr (stepBundleTree sp tr U ord ord') ∨
    ∃ i : Fin nNew, e ∈ lazyE i)

/-- **`AsmFsQ₄` with all its witnesses as arguments**: the witnesses of `AsmFsQ₃At` (the ends
`hEnd₂`, `hEnd₃` of Phases 2 and 3 are the values of their outcomes) and those of the post of
Phase 4 (`AsmFirstPhase4PostAt`). -/
def AsmFsQ₄At {depth : ℕ} (TS : BundleTourSpec) (impl : SparsifyImpl) (P L capExp limbMul w : ℕ)
    (Ψ : BundleTreeState depth → ℕ) (fVertRoot fInitOne fInitSpan : ℕ) (p : Program)
    (hRoot : AsmFirstTourRootAt TRc w p fVertRoot) (bBun bTourStep fDelTriples fBuildGroups : ℕ)
    (K : AsmFirstP4Code TRc w impl p fVertRoot)
    (A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth)
    (st₁ : State) (c₁ : ℕ) (st₂ : State) (c₂ : ℕ) (st₃ : State) (c₃ : ℕ)
    (o₄ : Outcome) (st₄ : State) (c₄ : ℕ)
    (hEnd₂ : ℕ) (y' : AsmBrSide scProgB5 depth) (tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ)
    (lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ) (hEnd₃ : ℕ)
    (tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (splitPtr outDescPtr : ℕ)
    (mk' : Finset End) (Mset : Finset ℕ) (Ys : List (List End)) (touched : List ℕ)
    (qs : List (SpanUpdTask × P4TaskOut)) (ns : List (ℕ × List ℕ))
    (x' : BucketSpannerMeta depth y'.cap) (yE : EmbConc)
    (tx' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (Ld Li Lr T₀ : List ℕ) : Prop :=
  AsmFsQ₃At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun bTourStep
      fDelTriples fBuildGroups A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr
      outDescPtr mk' Mset Ys touched ∧
  AsmFirstPhase4PostAt (asmBrSP impl w depth y') TRc K.HE.mul K.HE.querySpace hRoot.mul
      hRoot.querySpace y'.spanH hEnd₃ A.x.xRest.eCap5 A.x.xRest.vCap5 A.x.embH
      A.x.xRest.slots.length
      (A.x.xRest.slots.length + newCompsBucketSum A.tr A.x.xRest.comps
        (A.newComps A.x.xRest.cmpH A.x.xRest.comps))
      A.x.tourH A.h y'.spanS y'.xSpan (p4TasksOf st₃.mem (outDescPtr + 1) touched.length)
      A.x.yEmb.view A.x.yEmb A.U A.ed A.c lazyE mk' tx_pot'
      ((outGraphRep A.x.vCap A.x.eCap).foot A.x.outH A.x.gOut) st₃.mem A.tr A.ord o₄ st₄ c₄
      qs ns x' yE tx' Ld Li Lr T₀

/-- **The bundle side after the step**: the side `y'` after Phase 2, with the bundle table after
the step (`tableAfterStepRuns`, Phase 3), the spanners after the tasks that Phase 3 wrote at
`outDescPtr + 1` (`p4SpanAfter`, Phase 4) with their concrete state `x'`, and the value of the
walk potential `Ψ` at the new state of the model. The other fields are those of `y'`. -/
noncomputable def asmFsSideAfter
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)} {depth : ℕ}
    (impl : SparsifyImpl) (w : ℕ) (Ψ : BundleTreeState depth → ℕ) (tr : BundleTreeState depth)
    (U : List Update) (ord : ℕ → List End) (ed : List OrdEdit) (y' : AsmBrSide B5 depth)
    (mem₃ : ℕ → ℕ) (outDescPtr nTouched : ℕ) (x' : BucketSpannerMeta depth y'.cap) :
    AsmBrSide B5 depth :=
  { y' with
    bunS := tableAfterStepRuns tr.cs tr.k (applyOrdEdits ord ed) U y'.bunS
    spanS := p4SpanAfter (asmBrSP impl w depth y') y'.spanS mem₃
      (p4TasksOf mem₃ (outDescPtr + 1) nTouched)
    xSpan := x'
    walkPot := Ψ (stepBundleTree (fun _ => canonicalSparsify impl) tr U ord
      (applyOrdEdits ord ed)).state }

/-- **The post of one call without the cost**, for the return value `ov`, the final memory `mem'`
and the witnesses `yEmb`, `sTour`, `xTour`, `xRest`, `Ys`, `T₀`: every conjunct of `AsmFsPostRaw`
but the last. -/
def AsmFsPostNCAt {depth : ℕ} (TR : ℕ → ℕ → DSRep AsmTourAbs)
    (B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState))
    (impl : SparsifyImpl) (P L capExp limbMul w : ℕ) (Ψ : BundleTreeState depth → ℕ)
    (ysMul : ℕ) (space : ℕ → ℕ)
    (A : AsmFsArgs (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ depth)
    (ov : ℕ) (mem' : ℕ → ℕ) (yEmb : EmbConc) (sTour : OutTourAbs)
    (xTour : (TR A.x.vCap A.x.eCap).τ)
    (xRest : (asmBrSideRep B5 impl w depth L capExp limbMul Ψ).τ) (Ys : List (List End))
    (T₀ : List ℕ) : Prop :=
  let R := asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ
  let ord' := applyOrdEdits A.ord A.ed
  let sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut :=
    fun _ => canonicalSparsify impl
  let info := stepBundleTree sparsify A.tr A.U A.ord ord'
  let x₁ := A.x.afterCore yEmb sTour xTour xRest
  let avoid : ℕ → Prop := fun a =>
    (outGraphRep A.x.vCap A.x.eCap).foot A.x.outH A.x.gOut a ∨
      (TR A.x.vCap A.x.eCap).foot A.x.tourH xTour a
  (embRep A.x.eCap).rep A.x.embH yEmb.view yEmb mem' ∧
  (coreGraph info.state.cs.G info.state.cs.lsf).E ⊆ yEmb.view.dom ∧
  (∀ e ∈ (coreGraph info.state.cs.G info.state.cs.lsf).E,
    yEmb.view.emb e = info.state.emb e) ∧
  (asmBrTourView TR ⟨info.state, ord', A.x.vCap, A.x.eCap⟩ A.x.vCap A.x.eCap).rep A.x.tourH
    sTour xTour mem' ∧
  (∃ E₀ : Finset ℕ, outKeep sparsify A.tr A.U A.ord ord' ⊆ E₀ ∧ E₀ ⊆ A.tr.S_cur.E ∧
    OutMarksOf sTour (outCoreOrder info.state ord') E₀) ∧
  (asmBrSideRep B5 impl w depth L capExp limbMul Ψ).rep A.x.restH
    ⟨info.state, ord', A.x.vCap, A.x.eCap⟩ xRest mem' ∧
  xRest.slotCap = A.x.xRest.slotCap ∧ xRest.vCap5 = A.x.vCap ∧ xRest.eCap5 = A.x.eCap ∧
  AsmBrDisjoint (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) A.b x₁ ∧
  (∀ a, (asmBrPart (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) A.b A.x 0 a ∨
    asmBrPart (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) A.b A.x 1 a ∨
    asmBrPart (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) A.b A.x 3 a) →
    mem' a = A.mem a) ∧
  OutStepInAt mem' (mem' (A.h + ASM_ST_DEL)) (mem' (A.h + ASM_ST_SPLIT))
    (mem' (A.h + ASM_ST_INS)) ov avoid sparsify A.tr A.U A.ord ord' Ys ∧
  mem' (mem' (A.h + ASM_ST_ROT)) = T₀.length ∧
  ListAt mem' (mem' (A.h + ASM_ST_ROT) + 1) T₀ ∧
  OutCellsFree (mem' (A.h + ASM_ST_ROT)) (1 + T₀.length) ov avoid ∧
  T₀.Nodup ∧ (∀ v ∈ T₀, v < A.x.vCap) ∧ OutRotCover sparsify A.tr A.U A.ord ord' T₀ ∧
  readList mem' (mem' (A.h + ASM_ST_REEMB)) (mem' (A.h + ASM_ST_REEMBLEN)) =
    stepBundleTree_reembList sparsify A.tr A.U A.ord ord' ∧
  A.h + ASM_ST_SIZE ≤ mem' (A.h + ASM_ST_REEMB) ∧
  OutCellsFree (mem' (A.h + ASM_ST_REEMB)) (mem' (A.h + ASM_ST_REEMBLEN)) ov avoid ∧
  (∀ i < ASM_ST_SIZE, mem' (A.h + i) < 2 ^ w) ∧
  (Ys.map List.length).sum + T₀.length ≤
    ysMul * (A.tr.S_cur.batchEnc info.U_S + A.words + A.editWords + 1) *
      (Nat.log 2 (A.M + A.N + 2) + 1) ∧
  A.h + ASM_ST_SIZE ≤ ov ∧
  ov ≤ A.h + space (A.M + A.N + A.k + A.x.vCap + A.x.eCap + L + depth + A.words +
    A.editWords) ∧
  ZeroFrom mem' ov ∧
  (∀ a < A.h, ¬ R.foot A.b A.x a → mem' a = A.mem a) ∧
  (∀ a, R.foot A.b x₁ a → R.foot A.b A.x a ∨ (A.h + ASM_ST_SIZE ≤ a ∧ a < ov))

/-- **The cost of one call**, the last conjunct of `AsmFsPostRaw`, for the final memory `mem'`,
the cost `cost` and the new branch `x₁`: the cost plus the potential of `x₁` in `mem'` is at most
`mul` times the charge of the step of the model with the input words, plus the potential of the
old branch. -/
def AsmFsCostAt {depth : ℕ} (TR : ℕ → ℕ → DSRep AsmTourAbs)
    (B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState))
    (impl : SparsifyImpl) (P L capExp limbMul w : ℕ) (Ψ : BundleTreeState depth → ℕ)
    (mul : ℕ)
    (A : AsmFsArgs (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ depth)
    (mem' : ℕ → ℕ) (cost : ℕ)
    (x₁ : (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ) : Prop :=
  let R := asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ
  let sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut :=
    fun _ => canonicalSparsify impl
  cost + R.phi A.b x₁ mem' ≤
    mul * (branchStepCharge sparsify A.tr A.U A.ord (applyOrdEdits A.ord A.ed) +
      (A.words + A.editWords + 1) * bundleLogFactor A.M A.N) + R.phi A.b A.x A.mem

/-- **The cost goal of the first step.** For every call whose premises hold (`AsmFsPre`) and
every state after Phase 4 with its witnesses (`AsmFsQ₄At`), let `mem'` be the memory after
Phase 4 with the place of the split lists written at `h + 1` (what the driver does). Then the
cost `c₁ + c₂ + c₃ + c₄ + 340` of the four phases and the driver meets `AsmFsCostAt` for the
branch `A.x.afterCore yEmb sTour xTour xRest`, whose tour state `xTour` is the tour state `tx'`
of Phase 4 (at the caps of the branch, which equal those of the bundle side) and whose bundle side
`xRest` is `asmFsSideAfter`, for every `yEmb` and `sTour`. -/
def AsmFsCostGoal {depth : ℕ} (TS : BundleTourSpec) (impl : SparsifyImpl)
    (P L capExp limbMul wordExp w : ℕ) (Ψ : BundleTreeState depth → ℕ)
    (fVertRoot fInitOne fInitSpan : ℕ) (p : Program)
    (hRoot : AsmFirstTourRootAt TRc w p fVertRoot) (bBun bTourStep fDelTriples fBuildGroups : ℕ)
    (K : AsmFirstP4Code TRc w impl p fVertRoot) (mul : ℕ) (space : ℕ → ℕ) : Prop :=
  ∀ (A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth)
    (st₁ : State) (c₁ : ℕ) (st₂ : State) (c₂ : ℕ) (st₃ : State) (c₃ : ℕ)
    (o₄ : Outcome) (st₄ : State) (c₄ : ℕ)
    (hEnd₂ : ℕ) (y' : AsmBrSide scProgB5 depth) (tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ)
    (lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ) (hEnd₃ : ℕ)
    (tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (splitPtr outDescPtr : ℕ)
    (mk' : Finset End) (Mset : Finset ℕ) (Ys : List (List End)) (touched : List ℕ)
    (qs : List (SpanUpdTask × P4TaskOut)) (ns : List (ℕ × List ℕ))
    (x' : BucketSpannerMeta depth y'.cap) (yE : EmbConc)
    (tx' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (Ld Li Lr T₀ : List ℕ),
    AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
    AsmFsQ₄At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups K A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE
      hEnd₃ tx_pot' splitPtr outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ →
    ∀ xTour : (TRc A.x.vCap A.x.eCap).τ, HEq xTour tx' →
    ∀ (yEmb : EmbConc) (sTour : OutTourAbs),
      AsmFsCostAt TRc scProgB5 impl P L capExp limbMul w Ψ mul A
        (Function.update st₄.mem (A.h + 1) (st₃.mem hEnd₂)) (c₁ + c₂ + c₃ + c₄ + 340)
        (A.x.afterCore yEmb sTour xTour
          (asmFsSideAfter impl w Ψ A.tr A.U A.ord A.ed y' st₃.mem outDescPtr touched.length x'))

end

public section

/-- `AsmFirstPhase4Post` is `AsmFirstPhase4PostAt` for some witnesses. -/
theorem asmFirstPhase4Post_iff {P : DSParams} {cap : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {mulE qE mulR qR spanTbl hp eCap vCap embH lo hi tourH rec : ℕ}
    {S6 : BucketSpannerState cap} {x6 : BucketSpannerMeta P.L cap} {tasks : List SpanUpdTask}
    {v : EmbView} {y : EmbConc} {U : List Update} {ed : List OrdEdit} {c : LSFChange} {nNew : ℕ}
    {lazyE : Fin nNew → List ℕ} {mk : Finset End} {tx₀ : (TR vCap eCap).τ}
    {avoid₀ : ℕ → Prop} {mem₀ : ℕ → ℕ} {tr : BundleTreeState P.L} {ord : ℕ → List End}
    {o : Outcome} {st' : State} {cost : ℕ} :
    AsmFirstPhase4Post P TR mulE qE mulR qR spanTbl hp eCap vCap embH lo hi tourH rec S6 x6
        tasks v y U ed c lazyE mk tx₀ avoid₀ mem₀ tr ord o st' cost ↔
      ∃ qs ns x' y' tx' Ld Li Lr T₀,
        AsmFirstPhase4PostAt P TR mulE qE mulR qR spanTbl hp eCap vCap embH lo hi tourH rec S6
          x6 tasks v y U ed c lazyE mk tx₀ avoid₀ mem₀ tr ord o st' cost qs ns x' y' tx' Ld Li
          Lr T₀ :=
  Iff.rfl

/-- **`AsmFsQ₄` gives its witnesses**: the outcomes of Phases 2 and 3 are returns, and
`AsmFsQ₄At` holds for some witnesses. -/
theorem asmFsQ₄_at {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} {K : AsmFirstP4Code TRc w impl p fVertRoot}
    {A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth}
    {st₁ : State} {c₁ : ℕ} {o₂ : Outcome} {st₂ : State} {c₂ : ℕ} {o₃ : Outcome} {st₃ : State}
    {c₃ : ℕ} {o₄ : Outcome} {st₄ : State} {c₄ : ℕ}
    (hQ : AsmFsQ₄ TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups K A st₁ c₁ o₂ st₂ c₂ o₃ st₃ c₃ o₄ st₄ c₄) :
    ∃ hEnd₂, o₂ = .returned hEnd₂ ∧
    ∃ (y' : AsmBrSide scProgB5 depth) (tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ)
      (lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ),
    ∃ hEnd₃, o₃ = .returned hEnd₃ ∧
    ∃ (tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (splitPtr outDescPtr : ℕ)
      (mk' : Finset End) (Mset : Finset ℕ) (Ys : List (List End)) (touched : List ℕ)
      (qs : List (SpanUpdTask × P4TaskOut)) (ns : List (ℕ × List ℕ))
      (x' : BucketSpannerMeta depth y'.cap) (yE : EmbConc)
      (tx' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (Ld Li Lr T₀ : List ℕ),
      AsmFsQ₄At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
        bTourStep fDelTriples fBuildGroups K A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1
        lazyE hEnd₃ tx_pot' splitPtr outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr
        T₀ := by
  obtain ⟨hEnd₂, ho₂, y', tx1, lazyE, hEnd₃, ho₃, tx_pot', splitPtr, outDescPtr, mk', Mset, Ys,
    touched, hQ₃, hP4⟩ := hQ
  obtain ⟨qs, ns, x', yE, tx', Ld, Li, Lr, T₀, hP4'⟩ := asmFirstPhase4Post_iff.1 hP4
  exact ⟨hEnd₂, ho₂, y', tx1, lazyE, hEnd₃, ho₃, tx_pot', splitPtr, outDescPtr, mk', Mset, Ys,
    touched, qs, ns, x', yE, tx', Ld, Li, Lr, T₀, hQ₃, hP4'⟩

/-- **The post from its two parts**: the post without the cost and the cost, for the same
witnesses, give `AsmFsPost`. -/
theorem asmFsPost_of_nc_cost {depth : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {P L capExp limbMul w : ℕ} {Ψ : BundleTreeState depth → ℕ}
    {mul ysMul : ℕ} {space : ℕ → ℕ}
    {A : AsmFsArgs (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ depth}
    {ov : ℕ} {mem' : ℕ → ℕ} {cost : ℕ} {yEmb : EmbConc} {sTour : OutTourAbs}
    {xTour : (TR A.x.vCap A.x.eCap).τ}
    {xRest : (asmBrSideRep B5 impl w depth L capExp limbMul Ψ).τ} {Ys : List (List End)}
    {T₀ : List ℕ}
    (hNC : AsmFsPostNCAt TR B5 impl P L capExp limbMul w Ψ ysMul space A ov mem' yEmb sTour
      xTour xRest Ys T₀)
    (hC : AsmFsCostAt TR B5 impl P L capExp limbMul w Ψ mul A mem' cost
      (A.x.afterCore yEmb sTour xTour xRest)) :
    AsmFsPost TR B5 impl P L capExp limbMul w Ψ mul ysMul space A ov mem' cost := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28⟩ := hNC
  exact ⟨yEmb, sTour, xTour, xRest, Ys, T₀, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hC⟩

/-- A smaller cost meets `AsmFsCostAt` too. -/
theorem AsmFsCostAt.mono {depth : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {P L capExp limbMul w : ℕ} {Ψ : BundleTreeState depth → ℕ}
    {mul : ℕ}
    {A : AsmFsArgs (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ depth}
    {mem' : ℕ → ℕ} {cost cost' : ℕ}
    {x₁ : (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ}
    (h : AsmFsCostAt TR B5 impl P L capExp limbMul w Ψ mul A mem' cost x₁) (hle : cost' ≤ cost) :
    AsmFsCostAt TR B5 impl P L capExp limbMul w Ψ mul A mem' cost' x₁ := by
  unfold AsmFsCostAt at h ⊢
  exact le_trans (Nat.add_le_add_right hle _) h

/-- **The field `hPost` of `AsmFsPieces`** for `Q₄ := AsmFsQ₄`, from two named parts:
* `hNC`, the post without the cost (`AsmFsPostNCAt`), for the tour state `tx'` of Phase 4 and the
  bundle side `asmFsSideAfter`, with the other witnesses chosen by the prover;
* `hCost`, the cost goal (`AsmFsCostGoal`).
The tour state of the post lives at the caps of the branch; it is `tx'` cast along the equal caps
of the bundle side (`x.xRest.vCap5 = x.vCap`, `x.xRest.eCap5 = x.eCap`, from the rep). The cost of
the call is at most `c₁ + c₂ + c₃ + c₄ + 340` (`AsmFsCostAt.mono`). -/
theorem asmFirstStep_hPost_of {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} {K : AsmFirstP4Code TRc w impl p fVertRoot}
    {mul ysMul : ℕ} {space : ℕ → ℕ}
    (hNC : ∀ (A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp
        limbMul Ψ).τ depth)
      (st₁ : State) (c₁ : ℕ) (st₂ : State) (c₂ : ℕ) (st₃ : State) (c₃ : ℕ)
      (o₄ : Outcome) (st₄ : State) (c₄ : ℕ)
      (hEnd₂ : ℕ) (y' : AsmBrSide scProgB5 depth) (tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ)
      (lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ) (hEnd₃ : ℕ)
      (tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (splitPtr outDescPtr : ℕ)
      (mk' : Finset End) (Mset : Finset ℕ) (Ys : List (List End)) (touched : List ℕ)
      (qs : List (SpanUpdTask × P4TaskOut)) (ns : List (ℕ × List ℕ))
      (x' : BucketSpannerMeta depth y'.cap) (yE : EmbConc)
      (tx' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (Ld Li Lr T₀ : List ℕ),
      AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
      AsmFsQ₄At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
        bTourStep fDelTriples fBuildGroups K A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1
        lazyE hEnd₃ tx_pot' splitPtr outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr
        T₀ →
      ∀ xTour : (TRc A.x.vCap A.x.eCap).τ, HEq xTour tx' →
      ∃ (yEmb : EmbConc) (sTour : OutTourAbs) (Ys' : List (List End)) (T₀' : List ℕ),
        AsmFsPostNCAt TRc scProgB5 impl P L capExp limbMul w Ψ ysMul space A o₄.value
          (Function.update st₄.mem (A.h + 1) (st₃.mem hEnd₂)) yEmb sTour xTour
          (asmFsSideAfter impl w Ψ A.tr A.U A.ord A.ed y' st₃.mem outDescPtr touched.length x')
          Ys' T₀')
    (hCost : AsmFsCostGoal TS impl P L capExp limbMul wordExp w Ψ fVertRoot fInitOne fInitSpan p
      hRoot bBun bTourStep fDelTriples fBuildGroups K mul space) :
    ∀ A st₁ c₁ o₂ st₂ c₂ o₃ st₃ c₃ o₄ st₄ c₄,
      AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
      AsmFsQ₄ TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
        bTourStep fDelTriples fBuildGroups K A st₁ c₁ o₂ st₂ c₂ o₃ st₃ c₃ o₄ st₄ c₄ →
      ∀ mem', mem' = Function.update st₄.mem (A.h + 1) (st₃.mem o₂.value) →
      ∀ cost, cost ≤ c₁ + c₂ + c₃ + c₄ + 340 →
      AsmFsPost TRc scProgB5 impl P L capExp limbMul w Ψ mul ysMul space A o₄.value mem'
        cost := by
  intro A st₁ c₁ o₂ st₂ c₂ o₃ st₃ c₃ o₄ st₄ c₄ hA hQ mem' hmem' cost hcost
  obtain ⟨hEnd₂, rfl, y', tx1, lazyE, hEnd₃, rfl, tx_pot', splitPtr, outDescPtr, mk', Mset, Ys,
    touched, qs, ns, x', yE, tx', Ld, Li, Lr, T₀, hQ'⟩ := asmFsQ₄_at hQ
  have hR := hA.2.2.2.2.2.2.2.2.2.1
  have hcaps : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ = (TRc A.x.vCap A.x.eCap).τ := by
    rw [hR.2.1, hR.2.2.1]
  have hx : HEq (cast hcaps tx') tx' := cast_heq hcaps tx'
  obtain ⟨yEmb, sTour, Ys', T₀', hnc⟩ := hNC A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE
    hEnd₃ tx_pot' splitPtr outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ hA hQ'
    (cast hcaps tx') hx
  have hc := hCost A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr
    outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ hA hQ' (cast hcaps tx') hx yEmb
    sTour
  subst hmem'
  exact asmFsPost_of_nc_cost hnc (hc.mono hcost)

end

end MinCostFlow.SparseCore.Program
