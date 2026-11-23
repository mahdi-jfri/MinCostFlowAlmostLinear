module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase4Proof

import Mathlib.Tactic

/-!
# The post of Phase 4 as a predicate (`AssemblyFirstStepP4Post`)

The top proof of the first step (`AssemblyFirstStepTop`) passes the state from Phase 4 to the
post of the step through a predicate `Q₄`. Its main part is the post of Phase 4
(`asmFirstPhase4_runs_of_sel`), which this file names `AsmFirstPhase4Post`: it is that post for
the outcome `o`, the final state `st'` and the cost `cost`, word for word, with the multipliers
and the query spaces of the two tour procedures (`AsmFirstTourEndRootAt`, `AsmFirstTourRootAt`)
as arguments `mulE`, `qE`, `mulR`, `qR`. `asmFirstPhase4_runs_post` restates
`asmFirstPhase4_runs_of_sel` with it.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart
open MinCostFlow.SparseCore.Program.Read

@[expose] public section

/-- **The post of Phase 4** (`asmFirstPhase4_runs_of_sel`) for the outcome `o`, the final state
`st'` and the cost `cost`. -/
def AsmFirstPhase4Post (P : DSParams) {cap : ℕ} (TR : ℕ → ℕ → DSRep AsmTourAbs)
    (mulE qE mulR qR : ℕ) (spanTbl hp eCap vCap embH lo hi tourH rec : ℕ)
    (S6 : BucketSpannerState cap) (x6 : BucketSpannerMeta P.L cap) (tasks : List SpanUpdTask)
    (v : EmbView) (y : EmbConc) (U : List Update) (ed : List OrdEdit) (c : LSFChange) {nNew : ℕ}
    (lazyE : Fin nNew → List ℕ) (mk : Finset End) (tx₀ : (TR vCap eCap).τ)
    (avoid₀ : ℕ → Prop) (mem₀ : ℕ → ℕ) (tr : BundleTreeState P.L) (ord : ℕ → List End)
    (o : Outcome) (st' : State) (cost : ℕ) : Prop :=
  let sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify P.impl
  let ord' := applyOrdEdits ord ed
  let cs' := compLSFBatch tr.cs U
  ∃ (qs : List (SpanUpdTask × P4TaskOut)) (ns : List (ℕ × List ℕ))
    (x' : BucketSpannerMeta P.L cap) (y' : EmbConc) (tx' : (TR vCap eCap).τ)
    (Ld Li Lr T₀ : List ℕ),
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

end

public section

set_option maxHeartbeats 1600000 in
/-- **Phase 4 with its post named** (`asmFirstPhase4_runs_of_sel` with `AsmFirstPhase4Post`). -/
theorem asmFirstPhase4_runs_post {P : DSParams} {cap : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {fSelP fFront fSel fLists fEnds fDel fIns fCopyIns fEndRoot fRot fDirect fBatch fEdits
      fBuild fVertRoot fReemb fCopy bSort : ℕ} {p : Program}
    (HE : AsmFirstTourEndRootAt TR P.w p fEndRoot) (HR : AsmFirstTourRootAt TR P.w p fVertRoot)
    (hTR_loc : ∀ v e, (TR v e).Local)
    (hfSelP : p.procs[fSelP]? = some (asmFirstP4SelStmt fFront fSel))
    (hfLists : p.procs[fLists]? = some (asmFirstP4ListsStmt fEnds fDel fIns fCopyIns))
    (hfEnds : p.procs[fEnds]? = some (asmFirstQueryInsEndsStmt fEndRoot))
    (hfDel : p.procs[fDel]? = some (asmFirstBuildDelStmt bSort))
    (hfIns : p.procs[fIns]? = some (asmFirstBuildInsStmt bSort))
    (hfCopyIns : p.procs[fCopyIns]? = some asmFirstCopyInsStmt)
    (hfRot : p.procs[fRot]? = some (asmFirstP4RotStmt fDirect fBatch fEdits fBuild))
    (hfDirect : p.procs[fDirect]? = some asmFirstCollectRotDirectStmt)
    (hfBatch : p.procs[fBatch]? = some (asmFirstCollectRotBatchStmt fVertRoot))
    (hfEdits : p.procs[fEdits]? = some (asmFirstCollectRotEditsStmt fVertRoot))
    (hfBuild : p.procs[fBuild]? = some (asmFirstBuildRotStmt bSort))
    (hfReemb : p.procs[fReemb]? = some (asmFirstP4ReembStmt fCopy fBuild))
    (hfCopy : p.procs[fCopy]? = some asmFirstStrideCopyStmt)
    (hpS : p.HasAt bSort (sortProcs bSort))
    {spanTbl descPtr hp eCap vCap oldS embH lo hi batch chg lazyPtr nNew words tourH spPtr edits
      editWords rec pos : ℕ}
    {S6 : BucketSpannerState cap} {x6 : BucketSpannerMeta P.L cap} {tasks : List SpanUpdTask}
    {v : EmbView} {y : EmbConc} {G₀ : MGraph} {U : List Update} {ed : List OrdEdit}
    {c : LSFChange} {lazyE : Fin nNew → List ℕ} {mk : Finset End} {tx₀ : (TR vCap eCap).τ}
    {avoid₀ : ℕ → Prop} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    {tr : BundleTreeState P.L} {ord : ℕ → List End} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {o₁ : Outcome} {st₁ : State} {c₁ : ℕ}
    (hr₁ : Runs P.w p ω (asmFirstP4SelStmt fFront fSel)
      (startState [spanTbl, descPtr, tasks.length, hp, eCap, oldS, embH, lo, hi, batch, chg,
        lazyPtr, nNew] mem₀ pos) o₁ st₁ c₁)
    (hpost : P4SelPost P S6 x6 spanTbl hp eCap embH v y tasks lo hi tr U ord (applyOrdEdits ord ed)
      (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord (applyOrdEdits ord ed)) c lazyE
      mem₀ o₁ st₁ c₁)
    (hw16 : 16 ≤ 2 ^ P.w) (htour_w : tourH < 2 ^ P.w) (hvCap_w : vCap < 2 ^ P.w)
    (heCap_w : eCap < 2 ^ P.w)
    (hrepT : (TR vCap eCap).rep tourH ⟨applyOrdEdits ord ed, (compLSFBatch tr.cs U).RF, mk⟩ tx₀
      mem₀)
    (hfootT : ∀ x, (TR vCap eCap).foot tourH tx₀ x → x < hp)
    (hTB : ∀ x, (TR vCap eCap).foot tourH tx₀ x → ¬ bucketFoot spanTbl x6 x)
    (hTE : ∀ x, (TR vCap eCap).foot tourH tx₀ x → ¬ embFoot eCap embH y x)
    (hEmbF : ∀ x, embFoot eCap embH y x → x < hp)
    (hBF : ∀ x, bucketFoot spanTbl x6 x → x < hp)
    (hSp : SplitEntriesAt mem₀ spPtr (canonSplitList tr.cs U))
    (hBat : BatchAt mem₀ batch G₀ U words) (hEd : OrdEditsAt mem₀ edits ed editWords)
    (hInp : ∀ x, (spPtr ≤ x ∧ x < spPtr + splitEntriesWords (canonSplitList tr.cs U)) ∨
      (batch ≤ x ∧ x < batch + words) ∨ (edits ≤ x ∧ x < edits + editWords) →
      x < hp ∧ ¬ bucketFoot spanTbl x6 x ∧ ¬ embFoot eCap embH y x ∧
        ¬ (TR vCap eCap).foot tourH tx₀ x)
    (hrec : rec + 6 ≤ hp)
    (hrecF : ∀ i < 6, ¬ bucketFoot spanTbl x6 (rec + i) ∧ ¬ embFoot eCap embH y (rec + i) ∧
      ¬ (TR vCap eCap).foot tourH tx₀ (rec + i))
    (havoid : ∀ x, avoid₀ x → x < hp)
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hU : tr.cs.G.BatchIsValid U)
    (hOB : OrderedBatch tr.cs.G U ord (applyOrdEdits ord ed))
    (hModN : RestartScurModelInv
      (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord (applyOrdEdits ord ed)).state)
    (hLazyIff : ∀ e, (∃ i : Fin nNew, e ∈ lazyE i) ↔
      e ∈ (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord
        (applyOrdEdits ord ed)).newlyActive.biUnion
        fun C => (tr.activeBuckets C).biUnion fun b => (tr.bun (C, b)).edges)
    (hVU : ∀ v ∈ batchVerts U, v < vCap) (hVE : ∀ v ∈ ordEditVerts ed, v < vCap)
    (hVraw : ∀ v ∈ asmFirstRotRawSet (fun _ => canonicalSparsify P.impl) tr U ord ed, v < vCap)
    (hsp : hp + p4WsSize eCap + (tasks.map (p4TaskSpace P S6 mem₀)).sum +
      rangeCost (p4NewSpace P (p4SpanAfter P S6 mem₀ tasks)) lo hi +
      asmFirstPhase4Room vCap eCap (canonSplitList tr.cs U).length U.length ed.length HE.querySpace
        HR.querySpace < 2 ^ P.w) :
    ∃ o st' cost, Runs P.w p ω (asmFirstPhase4Stmt fSelP fLists fRot fReemb)
        (startState [spanTbl, descPtr, tasks.length, hp, eCap, oldS, embH, lo, hi, batch, chg,
          lazyPtr, nNew, tourH, spPtr, edits, rec] mem₀ pos) o st' cost ∧
      AsmFirstPhase4Post P TR HE.mul HE.querySpace HR.mul HR.querySpace spanTbl hp eCap vCap
        embH lo hi tourH rec S6 x6 tasks v y U ed c lazyE mk tx₀ avoid₀ mem₀ tr ord o st' cost :=
  asmFirstPhase4_runs_of_sel HE HR hTR_loc hfSelP hfLists hfEnds hfDel hfIns hfCopyIns hfRot
    hfDirect hfBatch hfEdits hfBuild hfReemb hfCopy hpS hr₁ hpost hw16 htour_w hvCap_w heCap_w
    hrepT hfootT hTB hTE hEmbF hBF hSp hBat hEd hInp hrec hrecF havoid hI hU hOB hModN hLazyIff
    hVU hVE hVraw hsp

end

end MinCostFlow.SparseCore.Program
