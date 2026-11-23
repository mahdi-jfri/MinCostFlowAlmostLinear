module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4SelHyps

import WordRAM.Tactic

/-!
# The selectors after the front of Phase 4 (`AssemblyFirstStepP4Sel`)

The builders of the output batch need three flag arrays: one for the leaving edges
(`outDelSet`), one for the leaving edges that stay in the new graph, and one for the entering
edges (`outInsSet`). The procedure `asmFirstMarkOutSelStmt` (`AssemblyFirstStepOutSel.lean`)
writes them from two candidate lists and from the flags of the workspace of Phase 4. This file
runs it right after the front of Phase 4.

The procedure `asmFirstP4SelStmt fFront fSel` takes the arguments of the front,
`[spanTbl, descPtr, n, hp, eCap, oldS, embH, lo, hi, batch, chg, lazyPtr, nNew]`. It calls the
front, which returns `h₁ + 3 * eCap` with the flags of the batch at `h₁`. Then it calls the
selectors on the lists `delSup` and `insSup` of the workspace at `hp`, the old output graph at
`oldS`, the flags of the batch at `h₁`, and the flags `inDtot`, `inAct`, `inTgt` of the
workspace. The selectors lie at `h₁ + 3 * eCap`, and the procedure returns `h₁ + 6 * eCap`.

The selectors decide the right sets because of `p4SpanWV_cover`: the lists of the
workspace contain the leaving and the entering edges, and the test that the selectors run on
each listed edge decides membership (`p4Sel_hyps`). The run lemma `asmFirstP4Sel_runs` takes the
hypotheses of the front, the slot model on the tasks (`P4SlotTasks`), the hypotheses of `p4SpanWV_cover` on
the model, the exact change record of the forest, and the lazy lists of the newly active
components. Its post `P4SelPost` keeps what the front leaves, adds the three selectors, and also
states that the lists contain the leaving and the entering edges, which the builders need.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart
open MinCostFlow.SparseCore.Program.Read

/-! ## The procedure and what it leaves -/

@[expose] public section

/-- **The front of Phase 4 and the selectors**, with the arguments of the front,
`[spanTbl, descPtr, n, hp, eCap, oldS, embH, lo, hi, batch, chg, lazyPtr, nNew]`. Register `13`
holds the pointer that the front returns, register `14` the place `h₁` of the flags of the batch,
and register `15` the pointer that the selectors return. -/
def asmFirstP4SelStmt (fFront fSel : ℕ) : Stmt :=
  .call 13 fFront [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
    .reg 10, .reg 11, .reg 12] ;;
  .assign 14 (.bin .sub (.reg 13) (.bin .mul (.const 3) (.reg 4))) ;;
  .call 15 fSel [.bin .add (.reg 3) (.bin .mul (.const 4) (.reg 4)),
    .load (.bin .add (.reg 3) (.bin .mul (.const 10) (.reg 4))),
    .bin .add (.reg 3) (.bin .mul (.const 6) (.reg 4)),
    .load (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 10) (.reg 4))) (.const 1)),
    .reg 5, .reg 14, .bin .add (.reg 14) (.reg 4), .bin .add (.reg 14) (.bin .mul (.const 2) (.reg 4)),
    .reg 3, .bin .add (.reg 3) (.reg 4), .bin .add (.reg 3) (.bin .mul (.const 2) (.reg 4)),
    .reg 4, .reg 13] ;;
  .ret (.reg 15)

/-- The edges that the spanner updates of a step re-embed: the sets `updateReembSet` of the
active pairs. -/
noncomputable def p4ReembSet (P : DSParams) (tr : BundleTreeState P.L)
    (info : BundleTreeStepInfo P.L) : Finset ℕ :=
  info.state.activeComps.biUnion fun C => (tr.activeBuckets C).biUnion fun b =>
    updateReembSet (tr.dyn (C, b)) (info.U_B (C, b)) (canonicalSparsify P.impl)

/-- What the front of Phase 4 and the selectors leave, for the step `info` of the branch `tr`
with the batch `U` and the orders `ord`, `ord'`. The witnesses are those of `P4FrontPost`. The
workspace at `hp` holds the workspace of the spanner part with the lists `Ld`, `Li`, `Lr`; `Ld`
holds the leaving edges, `Li` the entering edges, and `Lr` the re-embedded edges of the spanners
and the edges of the lazy lists. The three selectors lie at `h₁ + 3 * eCap`, `h₁ + 4 * eCap` and
`h₁ + 5 * eCap`, and the procedure returns `h₁ + 6 * eCap`. The cost is that of the front, plus
`115` per entry of the two lists, plus a constant. -/
def P4SelPost (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (x6 : BucketSpannerMeta P.L cap) (spanTbl hp eCap embH : ℕ) (v : EmbView) (y : EmbConc)
    (tasks : List SpanUpdTask) (lo hi : ℕ) (tr : BundleTreeState P.L) (U : List Update)
    (ord ord' : ℕ → List End) (info : BundleTreeStepInfo P.L) (c : LSFChange) {nNew : ℕ}
    (lazyE : Fin nNew → List ℕ) (mem₀ : ℕ → ℕ) (o : Outcome) (st' : State) (cost : ℕ) : Prop :=
  ∃ (qs : List (SpanUpdTask × P4TaskOut)) (ns : List (ℕ × List ℕ))
    (x' : BucketSpannerMeta P.L cap) (y' : EmbConc) (h₁ : ℕ) (Ld Li Lr : List ℕ),
    qs.map Prod.fst = tasks ∧ (∀ q ∈ qs, P4OutOK P S6 mem₀ q) ∧
    ns.map Prod.fst = List.range' lo (hi - lo) ∧
    (∀ q ∈ ns, ∀ (hs : q.1 < cap) (d : DSHist), p4SpanAfter P S6 mem₀ tasks ⟨q.1, hs⟩ = some d →
      q.2.Nodup ∧ q.2.toFinset = (d.state P).G.E) ∧
    Phase4WSAt st'.mem hp eCap
      { (p4SpanWV P S6 mem₀ tr.S_cur.E v tasks qs ns).1 with
        delSup := Ld, insSup := Li, reemb := Lr } ∧
    (∀ e, e ∈ Ld ↔ e ∈ (p4SpanWV P S6 mem₀ tr.S_cur.E v tasks qs ns).1.delSup ∨
      e ∈ batchDeletes U) ∧
    (∀ e, e ∈ Li ↔ e ∈ (p4SpanWV P S6 mem₀ tr.S_cur.E v tasks qs ns).1.insSup ∨
      e ∈ batchDeletes U ∨ e ∈ batchInsEdges U ∨ (∃ i : Fin nNew, e ∈ lazyE i) ∨ e ∈ c.fDel) ∧
    (∀ e, e ∈ Lr ↔ e ∈ p4ReembSet P tr info ∨ ∃ i : Fin nNew, e ∈ lazyE i) ∧
    (∀ e ∈ outDelSet (fun _ => canonicalSparsify P.impl) tr U ord ord', e ∈ Ld) ∧
    (∀ e ∈ outInsSet (fun _ => canonicalSparsify P.impl) tr U ord ord', e ∈ Li) ∧
    (embRep eCap).rep embH (p4SpanWV P S6 mem₀ tr.S_cur.E v tasks qs ns).2 y' st'.mem ∧
    (bucketSpannerRep P cap).rep spanTbl (p4SpanAfter P S6 mem₀ tasks) x' st'.mem ∧
    OutSelFlagsAt st'.mem (h₁ + 3 * eCap) eCap
      (outDelSet (fun _ => canonicalSparsify P.impl) tr U ord ord') ∧
    OutDelFlagsAt st'.mem (h₁ + 4 * eCap) eCap
      (info.state.cs.G.E ∩ outDelSet (fun _ => canonicalSparsify P.impl) tr U ord ord') ∧
    OutSelFlagsAt st'.mem (h₁ + 5 * eCap) eCap
      (outInsSet (fun _ => canonicalSparsify P.impl) tr U ord ord') ∧
    hp + p4WsSize eCap ≤ h₁ ∧
    h₁ ≤ hp + p4WsSize eCap + (tasks.map (p4TaskSpace P S6 mem₀)).sum +
      rangeCost (p4NewSpace P (p4SpanAfter P S6 mem₀ tasks)) lo hi ∧
    o.value = h₁ + 6 * eCap ∧
    ZeroFrom st'.mem (h₁ + 6 * eCap) ∧
    (∀ a < hp, ¬ bucketFoot spanTbl x6 a → ¬ embFoot eCap embH y a → st'.mem a = mem₀ a) ∧
    (∀ a, bucketFoot spanTbl x' a → bucketFoot spanTbl x6 a ∨ (hp + p4WsSize eCap ≤ a ∧ a < h₁)) ∧
    (∀ a, embFoot eCap embH y' a → embFoot eCap embH y a ∨ (hp + p4WsSize eCap ≤ a ∧ a < h₁)) ∧
    (∀ a, embFoot eCap embH y' a → ¬ bucketFoot spanTbl x' a) ∧
    cost + specPhi P (p4SpanAfter P S6 mem₀ tasks) ≤
      specPhi P S6 + (tasks.map fun t => p4TaskPay P S6 mem₀ t + 70).sum +
        rangeCost (fun s => p4NewPay P (p4SpanAfter P S6 mem₀ tasks) s + 20) lo hi +
        9 * (hi - lo) + 175 * U.length +
        130 * ((List.finRange nNew).map fun i => (lazyE i).length).sum + 90 * nNew +
        105 * c.fDel.length + 115 * (Ld.length + Li.length) + 620

end

public section

theorem asmFirstP4SelStmt_noRand (fFront fSel : ℕ) : (asmFirstP4SelStmt fFront fSel).NoRand := by
  simp [asmFirstP4SelStmt, Stmt.NoRand]

end

/-! ## The run -/

/-- The run of the statement from the runs of its two calls. -/
private theorem asmFirstP4Sel_run_of {w : ℕ} {p : Program} {ω : ℕ → Bool} {fFront fSel : ℕ}
    {bFront bSel : Stmt}
    (hfFront : p.procs[fFront]? = some bFront) (hfSel : p.procs[fSel]? = some bSel)
    {spanTbl descPtr n hp eCap oldS embH lo hi batch chg lazyPtr nNew pos h₁ lD lI : ℕ}
    {mem₀ : ℕ → ℕ} (hw16 : 16 ≤ 2 ^ w)
    {o₁ o₂ : Outcome} {st₁ st₂ : State} {c₁ c₂ : ℕ}
    (hr₁ : Runs w p ω bFront (startState [spanTbl, descPtr, n, hp, eCap, oldS, embH, lo, hi,
      batch, chg, lazyPtr, nNew] mem₀ pos) o₁ st₁ c₁)
    (hov : o₁.value = h₁ + 3 * eCap) (hsz : h₁ + 3 * eCap < 2 ^ w)
    (hws : hp + 10 * eCap + 1 < 2 ^ w)
    (hmD : st₁.mem (hp + 10 * eCap) = lD) (hmI : st₁.mem (hp + 10 * eCap + 1) = lI)
    (hr₂ : Runs w p ω bSel (startState [hp + 4 * eCap, lD, hp + 6 * eCap, lI, oldS, h₁,
      h₁ + eCap, h₁ + 2 * eCap, hp, hp + eCap, hp + 2 * eCap, eCap, o₁.value] st₁.mem st₁.pos)
      o₂ st₂ c₂) :
    ∃ st' c, Runs w p ω (asmFirstP4SelStmt fFront fSel)
        (startState [spanTbl, descPtr, n, hp, eCap, oldS, embH, lo, hi, batch, chg, lazyPtr, nNew]
          mem₀ pos) (.returned o₂.value) st' c ∧ st'.mem = st₂.mem ∧ c ≤ c₁ + c₂ + 100 := by
  have key : ∃ o st' c, Runs w p ω (asmFirstP4SelStmt fFront fSel)
      (startState [spanTbl, descPtr, n, hp, eCap, oldS, embH, lo, hi, batch, chg, lazyPtr, nNew]
        mem₀ pos) o st' c ∧ (o = .returned o₂.value ∧ st'.mem = st₂.mem) ∧
      0 + c ≤ c₁ + c₂ + 100 := by
    unfold asmFirstP4SelStmt
    refine p4_runs_seq_callRuns_le (by eval_expr) hfFront hr₁ ?_
    refine runs_seq_assign_le (v := h₁) ?_ ?_
    · exact Expr.eval_eq_of_eq (Expr.eval_sub (x := o₁.value) (y := 3 * eCap) (by eval_expr)
        (by eval_expr) (by omega)) (by omega)
    refine p4_runs_seq_callRuns_le (by eval_expr) hfSel hr₂ ?_
    wram_step
    · exact ⟨by simp, rfl⟩
    · wram_cost
  obtain ⟨o, st', c, hr, ⟨rfl, hm⟩, hc⟩ := key
  exact ⟨st', c, hr, hm, by omega⟩

/-- The flag of a removed forest edge, as a set: by the exact change record, the list `c.fDel`
holds the forest edges that leave. -/
private theorem p4_fDel_iff {L : ℕ} {tr : BundleTreeState L} {U : List Update} {c : LSFChange}
    (hcEx : c.Exact tr.cs.lsf (compLSFBatch tr.cs U).lsf) (e : ℕ) :
    e ∈ c.fDel ↔ e ∈ tr.cs.RF.F.E \ (compLSFBatch tr.cs U).RF.F.E := by
  rw [← List.mem_toFinset, hcEx.2.2.2]
  rfl

public section

set_option maxHeartbeats 1600000 in
/-- **The run of the front of Phase 4 and the selectors.** The hypotheses are those of the front
(`asmFirstP4Front_runs`), with the old output graph `tr.S_cur.E` at `oldS` and room for the
selectors in the space bound, and those of `p4SpanWV_cover` on the step `info` of the
branch `tr`. Besides, the tasks follow the slot model (`P4SlotTasks`), the change record `c` is
exact, and the lazy lists hold the edges of the bundles of the newly active components. Then
`asmFirstP4SelStmt` ends in `P4SelPost`. -/
theorem asmFirstP4Sel_runs {P : DSParams} {cap : ℕ}
    {fFront fSel fEval fSpan fSeed fFlags fSeedB fSeedL fAppend fLoop fNewLoop fNew bSpan fTask : ℕ}
    {fAfter fScanUH fScanD fScanR fDleft fCopy fEdge fPush fMark fScanNew bRead bCopy : ℕ}
    {p : Program}
    (hfFront : p.procs[fFront]? = some (asmFirstP4FrontStmt fSpan fSeed fFlags))
    (hfSel : p.procs[fSel]? = some (asmFirstMarkOutSelStmt fEval))
    (hfEval : p.procs[fEval]? = some asmFirstEvalTgtEStmt)
    (hfSpan : p.procs[fSpan]? = some (asmFirstP4SpanStmt fLoop fNewLoop))
    (hfSeed : p.procs[fSeed]? = some (asmFirstP4SeedStmt fSeedB fSeedL fAppend))
    (hfFlags : p.procs[fFlags]? = some asmFirstPrepFlagsStmt)
    (hfSeedB : p.procs[fSeedB]? = some (asmFirstSeedBatchStmt fPush))
    (hfSeedL : p.procs[fSeedL]? = some (asmFirstSeedLazyStmt fAppend))
    (hfAppend : p.procs[fAppend]? = some (asmFirstAppendListStmt fPush))
    (hfLoop : p.procs[fLoop]? = some (asmFirstP4LoopStmt fTask))
    (hfNewLoop : p.procs[fNewLoop]? = some (asmFirstP4NewLoopStmt fNew))
    (hpS : p.HasAt bSpan (bucketSpannerProcs P.impl bSpan))
    (hfTask : p.procs[fTask]? = some (asmFirstP4TaskStmt (bSpan + bsIdxOp0 + 1) fAfter))
    (hfAfter : p.procs[fAfter]? = some (asmFirstP4AfterStmt fScanUH fScanD fScanR fDleft fCopy))
    (hfUH : p.procs[fScanUH]? = some (asmFirstScanSlotUHStmt fEdge))
    (hfD : p.procs[fScanD]? = some (asmFirstScanSlotDStmt fPush fMark))
    (hfR : p.procs[fScanR]? = some (asmFirstScanSlotRStmt fPush))
    (hfDl : p.procs[fDleft]? = some (asmFirstScanDleftStmt fEdge (bRead + spanReadIdxPiWalkPtr)))
    (hfC : p.procs[fCopy]? = some (asmFirstCopySlotListStmt bCopy (bRead + spanReadIdxPiWalkPtr)))
    (hfEdge : p.procs[fEdge]? = some (asmFirstP4EdgeStmt fPush fMark))
    (hfPush : p.procs[fPush]? = some asmFirstPushDedupStmt)
    (hfMark : p.procs[fMark]? = some asmFirstMarkSlotEdgeStmt)
    (hfNew : p.procs[fNew]? = some (asmFirstP4NewStmt fScanNew fCopy))
    (hfN : p.procs[fScanNew]? = some (asmFirstScanNewSlotStmt fPush))
    (hcopy : p.HasAt bCopy [copyWords]) (hread : p.HasAt bRead spanReadoutProcs)
    {spanTbl descPtr hp eCap oldS embH lo hi batch chg lazyPtr nNew words pos : ℕ}
    {S6 : BucketSpannerState cap} {x6 : BucketSpannerMeta P.L cap} {tasks : List SpanUpdTask}
    {v : EmbView} {y : EmbConc} {G₀ : MGraph} {U : List Update}
    {c : LSFChange} {lazyE : Fin nNew → List ℕ} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    {tr : BundleTreeState P.L} {ord ord' : ℕ → List End} {info : BundleTreeStepInfo P.L}
    {slotOf : Finset ℕ × ℤ → ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    (hw16 : 16 ≤ 2 ^ P.w)
    (hBun : AsmFirstBunStepOut P cap S6 descPtr hp tasks mem₀)
    (hS6 : (bucketSpannerRep P cap).rep spanTbl S6 x6 mem₀)
    (hEmb : (embRep eCap).rep embH v y mem₀)
    (hOS : ∀ e < eCap, mem₀ (oldS + e) = if e ∈ tr.S_cur.E then 1 else 0)
    (hoIn : ∀ e < eCap, P4InCell spanTbl x6 eCap embH y hp (oldS + e)) (hoLe : oldS + eCap ≤ hp)
    (hdescIn : ∀ a, descPtr ≤ a → a < descPtr + 3 * tasks.length →
      P4InCell spanTbl x6 eCap embH y hp a)
    (hbatchIn : ∀ t ∈ tasks, ∀ a, t.batchPtr ≤ a → a < t.batchPtr + t.W →
      P4InCell spanTbl x6 eCap embH y hp a)
    (hcaps : ∀ t ∈ tasks, ∀ (hs : t.slot < cap) (d : DSHist), S6 ⟨t.slot, hs⟩ = some d →
      mem₀ t.batchPtr ≠ 0 → P4TaskCaps P eCap d (decodeBatch mem₀ t.batchPtr (d.state P).G).1)
    (hlo : lo ≤ hi) (hhiW : hi < 2 ^ P.w)
    (hslots : ∀ s, lo ≤ s → s < hi → ∃ (hs : s < cap) (d : DSHist),
      p4SpanAfter P S6 mem₀ tasks ⟨s, hs⟩ = some d ∧ ∀ e ∈ (d.state P).G.E, e < eCap)
    (heCap : eCap ≤ P.eCap)
    (hfoot : ∀ a, bucketFoot spanTbl x6 a → a < hp)
    (hEmbF : ∀ a, embFoot eCap embH y a → a < hp)
    (hDisj : ∀ a, embFoot eCap embH y a → ¬ bucketFoot spanTbl x6 a)
    (hBat : BatchAt mem₀ batch G₀ U words)
    (hCaps : ∀ u ∈ U, match u with
      | .insert e _ _ => e < eCap | .delete e => e < eCap | .split _ _ _ _ => True)
    (hBatIn : ∀ a, batch ≤ a → a < batch + words → P4InCell spanTbl x6 eCap embH y hp a)
    (hBat_le : batch + words ≤ hp)
    (hLazy : ∀ (i : Fin nNew), ∃ ptr, mem₀ (lazyPtr + 2 * i.1) = ptr ∧
      mem₀ (lazyPtr + 2 * i.1 + 1) = (lazyE i).length ∧ ListAt mem₀ ptr (lazyE i) ∧
      ptr + (lazyE i).length ≤ hp ∧ (∀ e ∈ lazyE i, e < eCap) ∧
      (∀ a, ptr ≤ a → a < ptr + (lazyE i).length → P4InCell spanTbl x6 eCap embH y hp a))
    (hLazyIn : ∀ a, lazyPtr ≤ a → a < lazyPtr + 2 * nNew → P4InCell spanTbl x6 eCap embH y hp a)
    (hLazy_le : lazyPtr + 2 * nNew ≤ hp)
    (hChg : LSFChangeAt mem₀ chg c) (hfDel_cap : ∀ e ∈ c.fDel, e < eCap)
    (hChgIn : ∀ a, chg ≤ a → a < chg + c.words → P4InCell spanTbl x6 eCap embH y hp a)
    (hChg_le : chg + c.words ≤ hp)
    (hz : ZeroFrom mem₀ hp)
    (hspace : hp + p4WsSize eCap + (tasks.map (p4TaskSpace P S6 mem₀)).sum +
      rangeCost (p4NewSpace P (p4SpanAfter P S6 mem₀ tasks)) lo hi + 6 * eCap < 2 ^ P.w)
    (hinfo : info = stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord')
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hU : tr.cs.G.BatchIsValid U)
    (hMod : RestartScurModelInv tr) (hBD : BunDisjointInv tr)
    (hMod' : RestartScurModelInv info.state) (hBD' : BunDisjointInv info.state)
    (hDynG' : ∀ p ∈ activePairs info.state, (info.state.dyn p).G.E = (info.state.bun p).edges)
    (hInactiveBkts : ∀ C ∈ components tr.cs.G₀, C ∉ tr.activeComps →
      ∀ e ∈ (tr.cs.compSt C).G.E \ (tr.cs.compSt C).RF.F.E,
        ∃ b ∈ tr.activeBuckets C, e ∈ (tr.bun (C, b)).edges)
    (hBunEdges : ∀ p ∈ activePairs info.state,
      (info.state.bun p).edges = (tr.bun p).edges \ batchDeletes U)
    (hHApply : ∀ p ∈ activePairs info.state,
      (tr.dyn p).H.applyBatch (info.stepOut p).UH = (info.state.dyn p).H)
    (hDynG : ∀ p ∈ activePairs tr, (tr.dyn p).G.E = (tr.bun p).edges)
    (hWalkNew : ∀ p ∈ activePairs info.state, p ∉ activePairs tr →
      ∀ g ∈ (info.state.dyn p).G.E, ∀ x ∈ walkEdges (piTotal (info.state.dyn p) g),
        x ∈ (info.state.dyn p).H.E)
    (hT : P4SlotTasks P tr info slotOf S6 mem₀ tasks lo hi)
    (hcEx : c.Exact tr.cs.lsf (compLSFBatch tr.cs U).lsf)
    (hN : ∀ e ∈ info.newlyActive.biUnion (fun C => (tr.activeBuckets C).biUnion fun b =>
      (tr.bun (C, b)).edges), ∃ i : Fin nNew, e ∈ lazyE i) :
    ∃ o st' cost, Runs P.w p ω (asmFirstP4SelStmt fFront fSel)
        (startState [spanTbl, descPtr, tasks.length, hp, eCap, oldS, embH, lo, hi, batch, chg,
          lazyPtr, nNew] mem₀ pos) o st' cost ∧
      P4SelPost P S6 x6 spanTbl hp eCap embH v y tasks lo hi tr U ord ord' info c lazyE mem₀ o st'
        cost := by
  classical
  have hsz : p4WsSize eCap = 11 * eCap + 4 := rfl
  -- The front.
  obtain ⟨o₁, st₁, c₁, hr₁, qs, ns, x₁, y₁, h₁, Ld, Li, Lr, hqs, hqsOK, hns, hnsOK, hW₁, hLd,
    hLi, hLr, hEmb₁, hS₁, hLO, hDB, hFD, hlo₁, hhi₁, hov₁, hz₁, hfr₁, hbf₁, hef₁, hdj₁, hc₁⟩ :=
    asmFirstP4Front_runs (pos := pos) (ω := ω) (OS := tr.S_cur.E) hfSpan hfSeed hfFlags hfSeedB
      hfSeedL hfAppend hfLoop hfNewLoop hpS hfTask hfAfter hfUH hfD hfR hfDl hfC hfEdge hfPush
      hfMark hfNew hfN hcopy hread hw16 hBun hS6 hEmb hOS hoIn hoLe hdescIn hbatchIn hcaps hlo
      hhiW hslots heCap hfoot hEmbF hDisj hBat hCaps hBatIn hBat_le hLazy hLazyIn hLazy_le hChg
      hfDel_cap hChgIn hChg_le hz (by omega)
  -- The model: `p4SpanWV_cover` and the hypotheses of the selectors.
  have hM := hT.model hqs hqsOK hns hnsOK
  subst hqs
  obtain ⟨hF1, hF2, hF3, hF4, hF5⟩ := p4SpanWV_cover hinfo hI hU hMod hBD hMod' hBD' hDynG'
    hInactiveBkts hBunEdges hHApply hDynG hWalkNew v hM
  subst hinfo
  have hcs : (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.cs =
      compLSFBatch tr.cs U := rfl
  have hfDelF : ∀ e, e ∈ c.fDel ↔ e ∈ tr.cs.RF.F.E \ (compLSFBatch tr.cs U).RF.F.E :=
    p4_fDel_iff hcEx
  obtain ⟨hDS_cov, hIS_cov, hDel_iff, hIns_iff⟩ := p4Sel_hyps hF1 hF2 hF3 hF4 hLd hLi
    (fun e he => (hfDelF e).mpr he) hN
  have hE'_iff : ∀ e ∈ outDelSet (fun _ => canonicalSparsify P.impl) tr U ord ord',
      e ∈ (compLSFBatch tr.cs U).G.E ↔ batchLastOp U e ≠ 2 := fun e he => by
    have heS : e ∈ tr.S_cur.E := (Finset.mem_sdiff.mp he).1
    have heG : e ∈ tr.cs.G.E := (Finset.mem_sdiff.mp (hMod.2.2.2.1.2.1 heS)).1
    rw [compLSFBatch_G]
    exact mem_applyBatch_E_of_mem_iff _ _ heG
  -- The memory after the front, as the selectors read it.
  set W := (p4SpanWV P S6 mem₀ tr.S_cur.E v (qs.map Prod.fst) qs ns).1 with hW
  have hDSb := hW₁.2.2.2.1
  have hISb := hW₁.2.2.2.2.1
  have hLdLen : Ld.length ≤ eCap := dedupBuf_length_le hDSb
  have hLiLen : Li.length ≤ eCap := dedupBuf_length_le hISb
  have hOld : ∀ e < eCap, st₁.mem (oldS + e) = if e ∈ tr.S_cur.E then 1 else 0 := fun e he => by
    have hin := hoIn e he
    rw [hfr₁ _ hin.1 hin.2.1 hin.2.2]; exact hOS e he
  have hFD' : ∀ e < eCap, st₁.mem (h₁ + 2 * eCap + e) =
      if e ∈ tr.cs.RF.F.E \ (compLSFBatch tr.cs U).RF.F.E then 1 else 0 := fun e he => by
    rw [hFD e he]
    by_cases hm : e ∈ c.fDel
    · simp only [hm, (hfDelF e).mp hm, ↓reduceIte]
    · simp only [hm, mt (hfDelF e).mpr hm, ↓reduceIte]
  have hz₁' : ZeroFrom st₁.mem o₁.value := by rw [hov₁]; exact hz₁
  -- The selectors, at the pointer that the front returns.
  obtain ⟨st₂, c₂, hr₂, hSD, hSE, hSI, hz₂, hfr₂, hc₂⟩ :=
    asmFirstMarkOutSel_runs (p := p) (pos := st₁.pos) (ω := ω) (h := o₁.value)
      (delSupPtr := hp + 4 * eCap) (insSupPtr := hp + 6 * eCap) (outEPres := oldS)
      (lastOpPtr := h₁) (inDelBPtr := h₁ + eCap) (inFDelPtr := h₁ + 2 * eCap) (inDtotPtr := hp)
      (inActPtr := hp + eCap) (inTgtPtr := hp + 2 * eCap) (eCap := eCap)
      (inOldS := tr.S_cur.E) (inDelB := batchDeletes U)
      (inFDel := tr.cs.RF.F.E \ (compLSFBatch tr.cs U).RF.F.E) (inDtot := W.inDtot)
      (inAct := W.inAct)
      (inTgt := W.inTgt) (outDelS := outDelSet (fun _ => canonicalSparsify P.impl) tr U ord ord')
      (outInsS := outInsSet (fun _ => canonicalSparsify P.impl) tr U ord ord')
      (E' := (compLSFBatch tr.cs U).G.E) (lastOp := batchLastOp U) (delSup := Ld) (insSup := Li)
      hfEval hw16 hDSb.2.2.2.1 (by simp only [hov₁]; omega) hDSb.2.1 hDS_cov hISb.2.2.2.1
      (by simp only [hov₁]; omega) hISb.2.1 hIS_cov hOld (by simp only [hov₁]; omega) hLO
      (by simp only [hov₁]; omega) hDB (by simp only [hov₁]; omega) hFD'
      (by simp only [hov₁]; omega) hW₁.1 (by simp only [hov₁]; omega) hW₁.2.1
      (by simp only [hov₁]; omega) hW₁.2.2.1 (by simp only [hov₁]; omega) hDel_iff hE'_iff
      hIns_iff hz₁' (by simp only [hov₁]; omega)
  -- The run of the whole statement.
  obtain ⟨st', cost, hrun, hm, hcost⟩ :=
    asmFirstP4Sel_run_of (lD := Ld.length) (lI := Li.length) (h₁ := h₁) hfFront hfSel hw16 hr₁
      hov₁ (by omega) (by omega) hDSb.2.2.1 hISb.2.2.1 hr₂
  -- The cells below the pointer of the front are kept.
  have hkeep : ∀ a < o₁.value, st'.mem a = st₁.mem a := fun a ha => by rw [hm]; exact hfr₂ a ha
  refine ⟨_, st', cost, hrun, qs, ns, x₁, y₁, h₁, Ld, Li, Lr, rfl, hqsOK, hns, hnsOK,
    phase4WSAt_of_agree hW₁ fun a _ h2 => hkeep a (by omega), hLd, hLi, fun e => ?_,
    hDS_cov, hIS_cov,
    (embRep_local eCap embH _ y₁ st₁.mem st'.mem fun a ha => ?_).1 hEmb₁,
    (bucketSpannerRep_local P cap spanTbl _ x₁ st₁.mem st'.mem fun a ha => ?_).1 hS₁,
    ?_, ?_, ?_, hlo₁, hhi₁, by show o₁.value + 3 * eCap = h₁ + 6 * eCap; omega, ?_, fun a ha hb he => ?_, hbf₁, hef₁, hdj₁, ?_⟩
  · rw [hLr e, hF5 e, p4ReembSet]
  · rcases hef₁ a ha with h | ⟨_, h2⟩
    · have := hEmbF a h; exact (hkeep a (by omega)).symm
    · exact (hkeep a (by omega)).symm
  · rcases hbf₁ a ha with h | ⟨_, h2⟩
    · have := hfoot a h; exact (hkeep a (by omega)).symm
    · exact (hkeep a (by omega)).symm
  · intro e he; rw [hm, show h₁ + 3 * eCap = o₁.value by omega]; exact hSD e he
  · intro e he; rw [hm, show h₁ + 4 * eCap = o₁.value + eCap by omega]; exact hSE e he
  · intro e he; rw [hm, show h₁ + 5 * eCap = o₁.value + 2 * eCap by omega]; exact hSI e he
  · rw [hm, show h₁ + 6 * eCap = o₁.value + 3 * eCap by omega]; exact hz₂
  · rw [hkeep a (by omega)]; exact hfr₁ a ha hb he
  · omega

end

end MinCostFlow.SparseCore.Program
