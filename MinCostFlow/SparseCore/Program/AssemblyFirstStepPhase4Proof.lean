module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase4Facts

import MinCostFlow.SparseCore.Program.AssemblyReemb
import WordRAM.Tactic

/-!
# The run of Phase 4 of the first step (`AssemblyFirstStepPhase4Proof`)

`asmFirstPhase4_runs_of_sel` is the run of `asmFirstPhase4Stmt`, from the run of its first call
(the front and the selectors, `asmFirstP4Sel_runs`, with `P4SelPost`). Taking this run as a
hypothesis keeps the statement short: the hypotheses of the front stay with
`asmFirstP4Sel_runs`, and the driver of the step (Phase 5) applies both lemmas.

After the selectors, the lemma runs the three other calls and proves the forms of the record that
the step of a branch needs (`AsmBrCoreStepAt`):
* the delete list: the leaving edges `outDelSet` in increasing order, with the flags of the new
  graph (`OutDelAt`, by `outDelAt_inter` from the flags of `E' ∩ outDelSet`);
* the insert list: the entering edges `outInsSet` in increasing order, with the new roots of
  their ends (`OutInsAt`, by `p4_ins_ord` and `outInsAt_congr` from the roots read in the tour);
* `T₀`, with `OutRotCover` (`p4_rot_cover`);
* the re-embedded list, equal to `stepBundleTree_reembList` (`p4_reemb_eq`).
The tour state of Phase 3, `⟨ord', cs'.RF, mk⟩`, is kept, the spanners and the embedding table
are those of the front (the table with the self-walks of the entering edges), and the cost is the
sum of the costs of the four calls.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart
open MinCostFlow.SparseCore.Program.Read

public section

set_option maxHeartbeats 4000000 in
/-- **The run of Phase 4.** From the run of the front and the selectors with `P4SelPost`, the
tour state `⟨ord', cs'.RF, mk⟩` of Phase 3 below `hp` and apart from the spanners and the
embedding table, the splits, the batch and the edits below `hp` outside every footprint, the
record below `hp`, the model facts of the step and room for Phase 4, the procedure
`asmFirstPhase4Stmt` writes the record of the step at `rec`. -/
theorem asmFirstPhase4_runs_of_sel {P : DSParams} {cap : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
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
    let sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify P.impl
    let ord' := applyOrdEdits ord ed
    let cs' := compLSFBatch tr.cs U
    ∃ o st' cost, Runs P.w p ω (asmFirstPhase4Stmt fSelP fLists fRot fReemb)
        (startState [spanTbl, descPtr, tasks.length, hp, eCap, oldS, embH, lo, hi, batch, chg,
          lazyPtr, nNew, tourH, spPtr, edits, rec] mem₀ pos) o st' cost ∧
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
            HE.querySpace HR.querySpace ∧
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
            (2 * (outInsSet sp tr U ord ord').card * (HE.mul * ordStoreLog eCap + 45) +
              35 * Li.length + outBuildCost Ld.length + outBuildCost Li.length +
              60 * (outInsSet sp tr U ord ord').card + 300) +
            p4RotCost (canonSplitList tr.cs U).length (outInsSet sp tr U ord ord').card U.length
              ed.length (p4RotRaw (canonSplitList tr.cs U)
                ((outInsSet sp tr U ord ord').sort (· ≤ ·))
                (fun e => cs'.RF.root (cs'.G.tail e)) (fun e => cs'.RF.root (cs'.G.head e))
                cs'.RF.root U ed).length vCap (HR.mul * ordStoreLog eCap + 60) +
            p4ReembCost (Lr.length + (outDelSet sp tr U ord ord').card) + 250 +
            (TR vCap eCap).phi tourH tx₀ mem₀ ∧
        Ld.Nodup ∧ Li.Nodup ∧ Lr.Nodup ∧
        (∀ e, e ∈ Ld ↔ e ∈ (p4SpanWV P S6 mem₀ tr.S_cur.E v tasks qs ns).1.delSup ∨
          e ∈ batchDeletes U) ∧
        (∀ e, e ∈ Li ↔ e ∈ (p4SpanWV P S6 mem₀ tr.S_cur.E v tasks qs ns).1.insSup ∨
          e ∈ batchDeletes U ∨ e ∈ batchInsEdges U ∨ (∃ i : Fin nNew, e ∈ lazyE i) ∨ e ∈ c.fDel) ∧
        (∀ e, e ∈ Lr ↔ e ∈ p4ReembSet P tr (stepBundleTree sp tr U ord ord') ∨
          ∃ i : Fin nNew, e ∈ lazyE i) := by
  intro sp ord' cs'
  classical
  obtain ⟨qs, ns, x', y₁, h₁, Ld, Li, Lr, hqs, hqsOK, hns, hnsOK, hW₁, hLd, hLi, hLr, hDelCov,
    hInsCov, hEmb₁, hS₁, hSelD, hE', hSelI, hh₁lo, hh₁hi, hov₁, hz₁, hfr₁, hbf₁, hef₁, hdj₁,
    hc₁⟩ := hpost
  obtain ⟨-, -, -, hDB, hIB, hRB, -⟩ := hW₁
  have hDB' : DedupBufAt st₁.mem (hp + 3 * eCap) (hp + 4 * eCap) (hp + 10 * eCap) eCap Ld := hDB
  have hIB' : DedupBufAt st₁.mem (hp + 5 * eCap) (hp + 6 * eCap) (hp + 10 * eCap + 1) eCap Li :=
    hIB
  have hRB' : DedupBufAt st₁.mem (hp + 7 * eCap) (hp + 8 * eCap) (hp + 10 * eCap + 2) eCap Lr :=
    hRB
  have hws : p4WsSize eCap = 11 * eCap + 4 := rfl
  have hLdLen : Ld.length ≤ eCap := p4_length_le_of_nodup_lt hDB'.1 hDB'.2.1
  have hLiLen : Li.length ≤ eCap := p4_length_le_of_nodup_lt hIB'.1 hIB'.2.1
  have hLrLen : Lr.length ≤ eCap := p4_length_le_of_nodup_lt hRB'.1 hRB'.2.1
  have hDcard : (outDelSet sp tr U ord ord').card ≤ Ld.length :=
    card_le_length_of_mem hDB'.1 hDelCov
  have hIcard : (outInsSet sp tr U ord ord').card ≤ Li.length :=
    card_le_length_of_mem hIB'.1 hInsCov
  have hDlen : ((outDelSet sp tr U ord ord').sort (· ≤ ·)).length =
      (outDelSet sp tr U ord ord').card := Finset.length_sort _
  have hIlen : ((outInsSet sp tr U ord ord').sort (· ≤ ·)).length =
      (outInsSet sp tr U ord ord').card := Finset.length_sort _
  unfold asmFirstPhase4Room at hsp
  have hRS : p4RotSpace vCap (canonSplitList tr.cs U).length (outInsSet sp tr U ord ord').card
      U.length ed.length HR.querySpace ≤
      p4RotSpace vCap (canonSplitList tr.cs U).length eCap U.length ed.length HR.querySpace := by
    unfold p4RotSpace; omega
  -- The tour and the inputs after the selectors.
  have hlocT₁ := hTR_loc vCap eCap tourH (⟨ord', cs'.RF, mk⟩ : AsmTourAbs) tx₀ mem₀ st₁.mem
    fun x hx => (hfr₁ x (hfootT x hx) (hTB x hx) (hTE x hx)).symm
  have hk₁ : ∀ x, (spPtr ≤ x ∧ x < spPtr + splitEntriesWords (canonSplitList tr.cs U)) ∨
      (batch ≤ x ∧ x < batch + words) ∨ (edits ≤ x ∧ x < edits + editWords) →
      st₁.mem x = mem₀ x := fun x hx => by
    obtain ⟨h1, h2, h3, -⟩ := hInp x hx
    exact hfr₁ x h1 h2 h3
  have hEmbF₁ : ∀ x, embFoot eCap embH y₁ x → x < h₁ + 6 * eCap := fun x hx => by
    rcases hef₁ x hx with h' | h'
    · have := hEmbF x h'; omega
    · omega
  have hET₁ : ∀ x, embFoot eCap embH y₁ x → ¬ (TR vCap eCap).foot tourH tx₀ x := fun x hx ht => by
    rcases hef₁ x hx with h' | h'
    · exact hTE x ht h'
    · have := hfootT x ht; omega
  -- 1. The output lists.
  have hAct : ∀ e ∈ outInsSet sp tr U ord ord',
      (∃ u, (e, true) ∈ ord' u) ∧ (∃ u, (e, false) ∈ ord' u) := fun e he =>
    (p4_ins_ord sp tr U ord ord' hOB hModN e he).1
  obtain ⟨o₂, st₂, c₂, hr₂, tx₂, y₂, hrepT₂, hDel₂, hFD₂, hIns₂, hFI₂, hdl₂, hil₂, hEmb₂, ho₂lo,
    ho₂hi, hz₂, hfr₂, hft₂, hef₂, hdj₂, hc₂⟩ :=
    asmFirstP4Lists_runs (h := h₁ + 6 * eCap) (pos := st₁.pos) (ω := ω)
      (insSupPtr := hp + 6 * eCap) (selInsPtr := h₁ + 5 * eCap) (delSupPtr := hp + 4 * eCap)
      (selDelPtr := h₁ + 3 * eCap) (inE'Ptr := h₁ + 4 * eCap) (avoid₀ := avoid₀)
      (Sdel := outDelSet sp tr U ord ord') (Sins := outInsSet sp tr U ord ord')
      (E' := cs'.G.E ∩ outDelSet sp tr U ord ord') (Ld := Ld) (Li := Li)
      (a := ⟨ord', cs'.RF, mk⟩) HE hTR_loc hfEnds hfDel hfIns hfCopyIns hpS hw16 htour_w
      (hlocT₁.1 hrepT) (fun x hx => by have := hfootT x hx; omega) hIB'.2.2.2.1 (by omega)
      hIB'.1 hIB'.2.1 hInsCov hSelI (by omega) hAct hDB'.2.2.2.1 (by omega) hDB'.2.1 hDelCov
      hSelD (by omega) hE' (by omega)
      (fun x hx => by have := hfootT x hx; omega) hEmb₁ hEmbF₁ hET₁
      (fun x hx => by have := havoid x hx; omega) heCap_w hz₁ (by unfold p4ListsSpace; omega)
  have hLS : p4ListsSpace eCap (outInsSet sp tr U ord ord').card Ld.length Li.length ≤
      6 + 18 * eCap := by
    unfold p4ListsSpace; omega
  have hft₂' : ∀ x, (TR vCap eCap).foot tourH tx₂ x → x < hp ∨
      (h₁ + 6 * eCap + 2 ≤ x ∧ x < o₂.value) := fun x hx => by
    rcases hft₂ x hx with h' | h'
    · exact Or.inl (hfootT x h')
    · exact Or.inr h'
  have hk₂ : ∀ x, x < hp → ¬ bucketFoot spanTbl x6 x → ¬ embFoot eCap embH y x →
      ¬ (TR vCap eCap).foot tourH tx₀ x → st₂.mem x = mem₀ x := fun x h1 hb he ht => by
    rw [hfr₂ x (by omega) ht fun hy => by
      rcases hef₁ x hy with h' | h'
      · exact he h'
      · omega]
    exact hfr₁ x h1 hb he
  -- The entering edges with the new roots of their ends.
  have hIns₂' : OutInsAt st₂.mem (st₂.mem (h₁ + 6 * eCap + 1))
      ((outInsSet sp tr U ord ord').sort (· ≤ ·))
      (fun e => cs'.RF.root (cs'.G.tail e)) (fun e => cs'.RF.root (cs'.G.head e)) := by
    refine outInsAt_congr hIns₂ fun e he => ?_
    have hS : e ∈ outInsSet sp tr U ord ord' := (Finset.mem_sort _).mp he
    obtain ⟨-, h1, h2⟩ := p4_ins_ord sp tr U ord ord' hOB hModN e hS
    refine ⟨?_, ?_⟩
    · show (if e ∈ outInsSet sp tr U ord ord' then cs'.RF.root (ordSrc ord' (e, true)) else 0) = _
      simp only [hS, ↓reduceIte]; rw [h1]
    · show (if e ∈ outInsSet sp tr U ord ord' then cs'.RF.root (ordSrc ord' (e, false)) else 0) = _
      simp only [hS, ↓reduceIte]; rw [h2]
  -- 2. The list `T₀`.
  have hT₂ : ∀ x, (TR vCap eCap).foot tourH tx₂ x →
      ¬ (x < hp ∧ ¬ (TR vCap eCap).foot tourH tx₀ x) :=
    fun x hx ⟨h1, h2⟩ => by
      rcases hft₂ x hx with h' | h'
      · exact h2 h'
      · omega
  have hkI₂ : ∀ x, (spPtr ≤ x ∧ x < spPtr + splitEntriesWords (canonSplitList tr.cs U)) ∨
      (batch ≤ x ∧ x < batch + words) ∨ (edits ≤ x ∧ x < edits + editWords) →
      st₂.mem x = mem₀ x := fun x hx => by
    obtain ⟨h1, h2, h3, h4⟩ := hInp x hx
    exact hk₂ x h1 h2 h3 h4
  have hw1 : 1 ≤ words := hBat.1
  have hew1 : 1 ≤ editWords := by rw [hEd.2.1]; omega
  have hSpW : splitEntriesWords (canonSplitList tr.cs U) =
      1 + 4 * (canonSplitList tr.cs U).length := rfl
  have hSp_lt : spPtr + splitEntriesWords (canonSplitList tr.cs U) ≤ hp := by
    have := (hInp (spPtr + splitEntriesWords (canonSplitList tr.cs U) - 1)
      (Or.inl ⟨by omega, by omega⟩)).1
    omega
  have hBat_lt : batch + words ≤ hp := by
    have := (hInp (batch + words - 1) (Or.inr (Or.inl ⟨by omega, by omega⟩))).1
    omega
  have hEd_lt : edits + editWords ≤ hp := by
    have := (hInp (edits + editWords - 1) (Or.inr (Or.inr ⟨by omega, by omega⟩))).1
    omega
  have hSp₂ : SplitEntriesAt st₂.mem spPtr (canonSplitList tr.cs U) :=
    splitEntriesAt_of_agree hSp fun x h1 h2 => hkI₂ x (Or.inl ⟨h1, h2⟩)
  have hBat₂ : BatchAt st₂.mem batch G₀ U words :=
    ⟨hBat.1, (hkI₂ batch (Or.inr (Or.inl ⟨le_rfl, by omega⟩))).trans hBat.2.1,
      batchBodyAt_of_agree hBat.2.2 fun x h1 h2 => hkI₂ x (Or.inr (Or.inl ⟨by omega, by omega⟩))⟩
  have hEd₂ : OrdEditsAt st₂.mem edits ed editWords :=
    ordEditsAt_of_agree hEd fun x h1 h2 => hkI₂ x (Or.inr (Or.inr ⟨h1, h2⟩))
  have hins : ((outInsSet sp tr U ord ord').sort (· ≤ ·)).toFinset =
      outInsSet sp tr U ord ord' := Finset.sort_toFinset _ _
  have hraw := rotAll_toFinset_eq_rawSet sp tr U ord ed hins
  have hraw_cap : ∀ v ∈ p4RotRaw (canonSplitList tr.cs U)
      ((outInsSet sp tr U ord ord').sort (· ≤ ·)) (fun e => cs'.RF.root (cs'.G.tail e))
      (fun e => cs'.RF.root (cs'.G.head e)) cs'.RF.root U ed, v < vCap := fun v hv => by
    apply hVraw
    rw [← hraw]
    exact List.mem_toFinset.mpr hv
  obtain ⟨o₃, st₃, c₃, hr₃, tx₃, hrepT₃, hcnt₃, hL₃, hFR₃, hge₃, ho₃lo, ho₃hi, hz₃, hfr₃, hft₃,
    hc₃⟩ :=
    asmFirstP4Rot_runs (h := o₂.value) (pos := st₂.pos) (ω := ω) (avoid₀ := avoid₀)
      (a := ⟨ord', cs'.RF, mk⟩) HR hTR_loc hfDirect hfBatch hfEdits hfBuild hpS hw16 htour_w
      hvCap_w hSp₂ (by omega) hIns₂' (by have := hFI₂.1; rw [hIlen]; omega) hBat₂ (by omega)
      hEd₂ (by omega)
      (fun x hx ht => by
        rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hT₂ x ht ⟨by omega, (hInp x (Or.inr (Or.inl ⟨h1, h2⟩))).2.2.2⟩
        · exact hT₂ x ht ⟨by omega, (hInp x (Or.inr (Or.inr ⟨h1, h2⟩))).2.2.2⟩)
      hVU hVE hraw_cap hrepT₂
      (fun x hx => by rcases hft₂' x hx with h' | h' <;> omega)
      (fun x hx hav => by have := havoid x hav; omega) hz₂
      (by rw [hIlen]; omega)
  have ho₃b : o₃.value + 2 + 8 * eCap ≤ h₁ + 6 * eCap + (6 + 18 * eCap) +
      p4RotSpace vCap (canonSplitList tr.cs U).length eCap U.length ed.length HR.querySpace +
      (2 + 8 * eCap) := by
    have h3 := ho₃hi
    rw [hIlen] at h3
    omega
  have hft₃' : ∀ x, (TR vCap eCap).foot tourH tx₃ x → x < hp ∨
      (h₁ + 6 * eCap + 2 ≤ x ∧ x < o₃.value) := fun x hx => by
    rcases hft₃ x hx with h' | h'
    · rcases hft₂' x h' with h'' | h''
      · exact Or.inl h''
      · right; omega
    · right; omega
  have hk₃ : ∀ x, x < o₂.value → ¬ (TR vCap eCap).foot tourH tx₂ x → st₃.mem x = st₂.mem x :=
    fun x h1 h2 => hfr₃ x h1 h2
  -- 3. The re-embedded list.
  have hnT₂ : ∀ x, x < h₁ + 6 * eCap + 2 → ¬ (TR vCap eCap).foot tourH tx₀ x →
      ¬ (TR vCap eCap).foot tourH tx₂ x := fun x h1 h2 ht => by
    rcases hft₂ x ht with h' | h'
    · exact h2 h'
    · omega
  have hk₂₁ : ∀ x, hp ≤ x → x < hp + 11 * eCap + 4 → st₂.mem x = st₁.mem x := fun x h1 h2 =>
    hfr₂ x (by omega) (fun ht => by have := hfootT x ht; omega) fun hy => by
      rcases hef₁ x hy with h' | h'
      · have := hEmbF x h'; omega
      · omega
  have hk₃₁ : ∀ x, hp ≤ x → x < hp + 11 * eCap + 4 → st₃.mem x = st₁.mem x :=
      fun x h1 h2 => by
    rw [hk₃ x (by omega) (hnT₂ x (by omega) fun ht => by have := hfootT x ht; omega)]
    exact hk₂₁ x h1 h2
  have hLr₃ : ListAt st₃.mem (hp + 8 * eCap) Lr :=
    hRB'.2.2.2.1.congr fun k h1 h2 => hk₃₁ k (by omega) (by omega)
  have hmR : st₃.mem (hp + 10 * eCap + 2) = Lr.length :=
    (hk₃₁ _ (by omega) (by omega)).trans hRB'.2.2.1
  have hDel₂' : OutDelAt st₂.mem (st₂.mem (h₁ + 6 * eCap))
      ((outDelSet sp tr U ord ord').sort (· ≤ ·)) cs'.G.E :=
    outDelAt_inter hDel₂ fun e he => (Finset.mem_sort _).mp he
  have hagD : ∀ x, st₂.mem (h₁ + 6 * eCap) ≤ x →
      x < st₂.mem (h₁ + 6 * eCap) + 1 + 2 * ((outDelSet sp tr U ord ord').sort (· ≤ ·)).length →
      st₃.mem x = st₂.mem x := fun x h1 h2 => by
    have hb := hFD₂.1
    refine hk₃ x (by omega) fun ht => ?_
    exact hFD₂.2 (x - st₂.mem (h₁ + 6 * eCap)) (by omega) (Or.inr (by
      rw [show st₂.mem (h₁ + 6 * eCap) + (x - st₂.mem (h₁ + 6 * eCap)) = x by omega]
      exact ht))
  have hDel₃ := outDelAt_of_agree hDel₂' hagD
  have hcap : ∀ e ∈ Lr ++ (outDelSet sp tr U ord ord').sort (· ≤ ·), e < eCap := fun e he => by
    rcases List.mem_append.mp he with h' | h'
    · exact hRB'.2.1 e h'
    · exact hDB'.2.1 e (hDelCov e ((Finset.mem_sort _).mp h'))
  obtain ⟨o₄, st₄, c₄, hr₄, hq₄, hL₄, hend₄, hge₄, ho₄lo, ho₄hi, hz₄, hfr₄, hc₄⟩ :=
    asmFirstP4Reemb_runs (h := o₃.value) (pos := st₃.pos) (ω := ω) hfCopy hfBuild hpS hw16
      heCap_w hLr₃ (by omega) hDel₃ (by have := hFD₂.1; rw [hDlen]; omega) hcap hz₃
      (by rw [hDlen]; omega)
  have ho₄b : o₄.value ≤ o₃.value + 2 + 8 * eCap := by
    have h4 := ho₄hi
    rw [hDlen] at h4
    omega
  -- 4. The run of the whole statement.
  have hmL : st₃.mem (h₁ + 6 * eCap) = st₂.mem (h₁ + 6 * eCap) :=
    hk₃ _ (by omega) (hnT₂ _ (by omega) fun ht => by have := hfootT _ ht; omega)
  obtain ⟨st', cost, hrun, hm', hcost⟩ := asmFirstPhase4_run_of (rec := rec) (tourH := tourH)
    (spPtr := spPtr) (edits := edits)
    (pos := pos) hfSelP hfLists hfRot hfReemb hw16
    (by omega) (by omega) (by omega) hr₁ hov₁ hIB'.2.2.1 hDB'.2.2.1 hr₂ rfl hr₃ hmR hmL hr₄
    (by omega)
  -- 5. The words of the record and the cells that the last steps keep.
  have hov₄ : (Outcome.returned o₄.value).value = o₄.value := rfl
  have hm4 : ∀ x, (x < rec ∨ rec + 6 ≤ x) → st'.mem x = st₄.mem x := fun x hx => by
    rw [hm']; exact p4RecordMem_of_ne hx
  have hkeep₃ : ∀ x, x < o₃.value → (x < rec ∨ rec + 6 ≤ x) → st'.mem x = st₃.mem x :=
    fun x h1 h2 => (hm4 x h2).trans (hfr₄ x h1)
  have hkeep₂ : ∀ x, x < o₂.value → ¬ (TR vCap eCap).foot tourH tx₂ x →
      (x < rec ∨ rec + 6 ≤ x) → st'.mem x = st₂.mem x := fun x h1 h2 h3 =>
    (hkeep₃ x (by omega) h3).trans (hk₃ x h1 h2)
  have hkeep₁ : ∀ x, x < h₁ + 6 * eCap → ¬ (TR vCap eCap).foot tourH tx₀ x →
      ¬ embFoot eCap embH y₁ x → (x < rec ∨ rec + 6 ≤ x) → st'.mem x = st₁.mem x :=
    fun x h1 h2 h3 h4 =>
      (hkeep₂ x (by omega) (hnT₂ x (by omega) h2) h4).trans (hfr₂ x h1 h2 h3)
  have hrecN : ∀ x, rec ≤ x → x < rec + 6 → ¬ bucketFoot spanTbl x6 x ∧
      ¬ embFoot eCap embH y x ∧ ¬ (TR vCap eCap).foot tourH tx₀ x := fun x h1 h2 => by
    have := hrecF (x - rec) (by omega)
    rwa [show rec + (x - rec) = x by omega] at this
  have hout : ∀ x, ¬ (rec ≤ x ∧ x < rec + 6) → (x < rec ∨ rec + 6 ≤ x) := fun x h => by omega
  have hR0 : st'.mem rec = st₂.mem (h₁ + 6 * eCap) := by
    rw [hm', p4RecordMem_rec, hfr₄ (h₁ + 6 * eCap) (by omega), hmL]
  have hR2 : st'.mem (rec + 2) = st₂.mem (h₁ + 6 * eCap + 1) := by
    rw [hm', p4RecordMem_ins, hfr₄ (h₁ + 6 * eCap + 1) (by omega),
      hk₃ (h₁ + 6 * eCap + 1) (by omega)
        (hnT₂ _ (by omega) fun ht => by have := hfootT _ ht; omega)]
  have hR3 : st'.mem (rec + 3) = st₃.mem o₂.value := by
    rw [hm', p4RecordMem_rot, hfr₄ o₂.value (by omega)]
  have hR4 : st'.mem (rec + 4) = st₄.mem o₃.value + 1 := by
    rw [hm', p4RecordMem_reemb]
  have hR5 : st'.mem (rec + 5) = st₄.mem (st₄.mem o₃.value) := by
    rw [hm', p4RecordMem_reembLen]
  -- The cells of the three structures are kept.
  have hT₃ : ∀ x, (TR vCap eCap).foot tourH tx₃ x →
      (TR vCap eCap).foot tourH tx₀ x ∨ (h₁ + 6 * eCap + 2 ≤ x ∧ x < o₃.value) := fun x hx => by
    rcases hft₃ x hx with h' | h'
    · rcases hft₂ x h' with h'' | h''
      · exact Or.inl h''
      · right; omega
    · right; omega
  have hlocT₃ := hTR_loc vCap eCap tourH (⟨ord', cs'.RF, mk⟩ : AsmTourAbs) tx₃ st₃.mem st'.mem
    fun x hx => by
      rcases hT₃ x hx with h' | h'
      · exact (hkeep₃ x (by have := hfootT x h'; omega)
          (hout x fun ⟨h1, h2⟩ => (hrecN x h1 h2).2.2 h')).symm
      · exact (hkeep₃ x h'.2 (Or.inr (by omega))).symm
  have hlocB := bucketSpannerRep_local P cap spanTbl (p4SpanAfter P S6 mem₀ tasks) x' st₁.mem
    st'.mem fun a ha => by
      have hy : ¬ embFoot eCap embH y₁ a := fun hy => hdj₁ a hy ha
      rcases hbf₁ a ha with h' | h'
      · have := hBF a h'
        exact (hkeep₁ a (by omega) (fun ht => hTB a ht h') hy
          (hout a fun ⟨h1, h2⟩ => (hrecN a h1 h2).1 h')).symm
      · exact (hkeep₁ a (by omega) (fun ht => by have := hfootT a ht; omega) hy
          (Or.inr (by omega))).symm
  have hagE : ∀ a, embFoot eCap embH y₂ a → st₂.mem a = st'.mem a := fun a ha => by
    have ht : ¬ (TR vCap eCap).foot tourH tx₂ a := hdj₂ a ha
    rcases hef₂ a ha with h' | h'
    · rcases hef₁ a h' with h'' | h''
      · have := hEmbF a h''
        exact (hkeep₂ a (by omega) ht (hout a fun ⟨h1, h2⟩ => (hrecN a h1 h2).2.1 h'')).symm
      · exact (hkeep₂ a (by omega) ht (Or.inr (by omega))).symm
    · exact (hkeep₂ a h'.2 ht (Or.inr (by omega))).symm
  have hq₃ := hFR₃.1
  have hgq₃ := hge₃
  have hgq₄ := hge₄
  have hend := hend₄
  -- 6. The forms of the record.
  refine ⟨.returned o₄.value, st', cost, hrun, qs, ns, x', y₂, tx₃, Ld, Li, Lr,
    (p4RotRaw (canonSplitList tr.cs U) ((outInsSet sp tr U ord ord').sort (· ≤ ·))
      (fun e => cs'.RF.root (cs'.G.tail e)) (fun e => cs'.RF.root (cs'.G.head e))
      cs'.RF.root U ed).toFinset.sort (· ≤ ·), ?_⟩
  intro avoid
  refine ⟨hqs, hqsOK, hns, hnsOK, hlocB.1 hS₁, (embRep_local eCap embH _ y₂ st₂.mem st'.mem hagE).1
    hEmb₂, hlocT₃.1 hrepT₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Finset.sort_nodup _ _, ?_,
    p4_rot_cover sp tr U ord ed hI hU hOB hins,
    by rw [Finset.length_sort]; exact List.toFinset_card_le _, ?_, ?_, ?_, hLdLen, hLiLen, hLrLen,
    by rw [hR0]; omega, by rw [hR2]; omega, by rw [hR3]; omega, by omega,
    by unfold asmFirstPhase4Room; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hDB'.1, hIB'.1, hRB'.1, hLd, hLi, hLr⟩
  · -- The delete list.
    rw [hR0]
    refine outDelAt_of_agree hDel₃ fun x h1 h2 => hkeep₃ x ?_ (Or.inr ?_)
    · have := hFD₂.1; rw [hDlen] at h2; omega
    · have := hdl₂; omega
  · rw [hR0]
    refine outCellsFree_mono hFD₂ (by omega) fun i hi hav => ?_
    rcases hav with h' | h'
    · exact Or.inl h'
    · rcases hft₃ _ h' with h'' | h''
      · exact Or.inr h''
      · have := hFD₂.1; omega
  · -- The insert list.
    rw [hR2]
    refine outInsAt_of_agree hIns₂' fun x h1 h2 => ?_
    have hb := hFI₂.1
    rw [hIlen] at h2
    refine hkeep₂ x (by omega) (fun ht => hFI₂.2 (x - st₂.mem (h₁ + 6 * eCap + 1)) (by omega)
      (Or.inr ?_)) (Or.inr (by have := hil₂; omega))
    rw [show st₂.mem (h₁ + 6 * eCap + 1) + (x - st₂.mem (h₁ + 6 * eCap + 1)) = x by omega]
    exact ht
  · rw [hR2]
    refine outCellsFree_mono hFI₂ (by omega) fun i hi hav => ?_
    rcases hav with h' | h'
    · exact Or.inl h'
    · rcases hft₃ _ h' with h'' | h''
      · exact Or.inr h''
      · have := hFI₂.1; omega
  · -- The list `T₀`.
    rw [hR3, hkeep₃ (st₃.mem o₂.value) (by omega) (Or.inr (by omega))]
    exact hcnt₃
  · rw [hR3]
    exact hL₃.congr fun k h1 h2 => hkeep₃ k (by omega) (Or.inr (by omega))
  · rw [hR3]
    exact outCellsFree_mono hFR₃ (by omega) fun i hi hav => hav
  · exact fun v hv => hraw_cap v (List.mem_toFinset.mp ((Finset.mem_sort _).mp hv))
  · -- The re-embedded list.
    have hL₄' := hL₄.congr (mem' := st'.mem) fun k h1 h2 => hm4 k (Or.inr (by omega))
    rw [hR4, hR5, hq₄, readList_of_listAt hL₄']
    exact p4_reemb_eq P tr U ord ord' lazyE hLr hLazyIff
  · rw [hR4]; omega
  · rw [hR4, hR5, hq₄]
    refine ⟨by omega, fun i hi hav => ?_⟩
    rcases hav with h' | h'
    · have := havoid _ h'; omega
    · rcases hT₃ _ h' with h'' | h''
      · have := hfootT _ h''; omega
      · omega
  · exact fun x hx => by rw [hm4 x (Or.inr (by omega))]; exact hz₄ x (by omega)
  · -- The frame.
    exact fun a ha hb he ht hr => (hkeep₁ a (by omega) ht (fun hy => by
      rcases hef₁ a hy with h' | h'
      · exact he h'
      · omega) hr).trans (hfr₁ a ha hb he)
  · -- The cells of the structures.
    exact fun a ha => by
      rcases hbf₁ a ha with h' | h'
      · exact Or.inl h'
      · right; omega
  · exact fun a ha => by
      rcases hef₂ a ha with h' | h'
      · rcases hef₁ a h' with h'' | h''
        · exact Or.inl h''
        · right; omega
      · right; omega
  · exact fun a ha => by
      rcases hT₃ a ha with h' | h'
      · exact Or.inl h'
      · right; omega
  · exact fun a hy hb => by
      rcases hef₂ a hy with h' | h'
      · exact hdj₁ a h' hb
      · rcases hbf₁ a hb with h'' | h''
        · have := hBF a h''; omega
        · omega
  · exact fun a hy ht => by
      rcases hft₃ a ht with h' | h'
      · exact hdj₂ a hy h'
      · rcases hef₂ a hy with h'' | h''
        · rcases hef₁ a h'' with h3 | h3
          · have := hEmbF a h3; omega
          · omega
        · omega
  · exact fun a hb ht => by
      rcases hbf₁ a hb with h' | h'
      · rcases hT₃ a ht with h'' | h''
        · exact hTB a h'' h'
        · have := hBF a h'; omega
      · rcases hT₃ a ht with h'' | h''
        · have := hfootT a h''; omega
        · omega
  · -- The cost.
    have hc₃' : c₃ + (TR vCap eCap).phi tourH tx₃ st₃.mem ≤
        p4RotCost (canonSplitList tr.cs U).length (outInsSet sp tr U ord ord').card U.length
          ed.length (p4RotRaw (canonSplitList tr.cs U) ((outInsSet sp tr U ord ord').sort (· ≤ ·))
            (fun e => cs'.RF.root (cs'.G.tail e)) (fun e => cs'.RF.root (cs'.G.head e))
            cs'.RF.root U ed).length vCap (HR.mul * ordStoreLog eCap + 60) +
          (TR vCap eCap).phi tourH tx₂ st₂.mem := by
      have h := hc₃; rw [hIlen] at h; exact h
    have hc₄' : c₄ ≤ p4ReembCost (Lr.length + (outDelSet sp tr U ord ord').card) := by
      have h := hc₄; rw [hDlen] at h; exact h
    have hp₁ := hlocT₁.2
    have hp₃ := hlocT₃.2
    omega

end

end MinCostFlow.SparseCore.Program
