module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4Span
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4Seed
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepOutFlags

import WordRAM.Tactic

/-!
# The front of Phase 4 (`AssemblyFirstStepP4Front`)

Phase 4 keeps its candidate lists and flags in a workspace of `p4WsSize eCap` words
(`Phase4WSAt`). The front of Phase 4 puts this workspace at the heap pointer `hp`, where memory is
zero, so the workspace starts empty (`phase4WSAt_zero`). Then the procedure
`asmFirstP4FrontStmt fSpan fSeed fFlags`, with arguments
`[spanTbl, descPtr, n, hp, eCap, oldS, embH, lo, hi, batch, chg, lazyPtr, nNew]`:
1. runs the spanner part (`asmFirstP4SpanStmt`, `AssemblyFirstStepP4Span.lean`) with the heap
   pointer `hp + p4WsSize eCap`;
2. puts the seeds into the candidate lists (`asmFirstP4SeedStmt`, `AssemblyFirstStepP4Seed.lean`);
3. writes the three flag arrays of the batch at the heap pointer `h₁` that the spanner part
   returns (`asmFirstPrepFlagsStmt`, `AssemblyFirstStepOutFlags.lean`): the last operation on each
   edge, the deleted edges, and the forest edges that leave.

The spanner part runs first, so its model is taken on the memory at the start. The seeds and the
flags read only input cells, which the spanner part keeps.

`asmFirstP4Front_runs` gives `P4FrontPost`: what the spanner part leaves, with the seeds in the
lists and the flags at `h₁`. The heap pointer it returns is `h₁ + 3 * eCap`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Read MinCostFlow.SparseCore.Program.Restart

/-! ## The procedure and what it leaves -/

@[expose] public section

/-- **The front of Phase 4**,
`[spanTbl, descPtr, n, hp, eCap, oldS, embH, lo, hi, batch, chg, lazyPtr, nNew]`. Register `13`
holds `hp + p4WsSize eCap`, register `14` the heap pointer after the spanner part, and register
`15` the heap pointer after the flags. -/
def asmFirstP4FrontStmt (fSpan fSeed fFlags : ℕ) : Stmt :=
  .assign 13 (.bin .add (.reg 3) (.bin .add (.bin .mul (.const 11) (.reg 4)) (.const 4))) ;;
  .call 14 fSpan [.reg 0, .reg 1, .reg 2, .reg 13, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8] ;;
  .call 15 fSeed [.reg 9, .reg 10, .reg 3, .reg 4, .reg 11, .reg 12] ;;
  .call 15 fFlags [.reg 9, .reg 10, .reg 4, .reg 14] ;;
  .ret (.reg 15)

/-- The workspace and the embedding view after the spanner part of Phase 4, from the empty
workspace: the tasks `qs` with their outputs, then the new slots `ns`. -/
noncomputable def p4SpanWV (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) (OS : Finset ℕ) (v : EmbView) (tasks : List SpanUpdTask)
    (qs : List (SpanUpdTask × P4TaskOut)) (ns : List (ℕ × List ℕ)) : Phase4WS × EmbView :=
  ns.foldl (p4NewStep P (p4SpanAfter P S6 mem₀ tasks))
    (qs.foldl (p4WVStep P S6 mem₀ OS) (⟨∅, ∅, ∅, [], [], [], ∅, []⟩, v))

/-- A cell that the front of Phase 4 reads and keeps: it lies below the heap pointer `hp`,
outside the spanners and outside the embedding table. -/
def P4InCell {L cap : ℕ} (spanTbl : ℕ) (x6 : BucketSpannerMeta L cap) (eCap embH : ℕ)
    (y : EmbConc) (hp a : ℕ) : Prop :=
  a < hp ∧ ¬ bucketFoot spanTbl x6 a ∧ ¬ embFoot eCap embH y a

/-- What the front of Phase 4 leaves, from the memory `mem₀`, the spanners `S6` (meta `x6`) and
the embedding table `v` (concrete data `y`). The lists `qs` and `ns` are those of the spanner part
(`P4SpanPost`). The workspace at `hp` holds the workspace of `p4SpanWV`, with the seeds of the
batch `U`, of the lists `lazyE` and of the change record `c` added to the candidate lists. The
flags of the batch lie at the heap pointer `h₁` that the spanner part returns, and the front
returns `h₁ + 3 * eCap`. The cells below `hp` outside the spanners and the table are kept, the
footprints grow only in `[hp + p4WsSize eCap, h₁)`, and the cost is paid as in the spanner part,
plus the seeds and the flags. -/
def P4FrontPost (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (x6 : BucketSpannerMeta P.L cap) (spanTbl hp eCap embH : ℕ) (OS : Finset ℕ) (v : EmbView)
    (y : EmbConc) (tasks : List SpanUpdTask) (lo hi : ℕ) (U : List Update) (c : LSFChange)
    {nNew : ℕ} (lazyE : Fin nNew → List ℕ) (mem₀ : ℕ → ℕ) (o : Outcome) (st' : State)
    (cost : ℕ) : Prop :=
  ∃ (qs : List (SpanUpdTask × P4TaskOut)) (ns : List (ℕ × List ℕ))
    (x' : BucketSpannerMeta P.L cap) (y' : EmbConc) (h₁ : ℕ) (Ld Li Lr : List ℕ),
    qs.map Prod.fst = tasks ∧ (∀ q ∈ qs, P4OutOK P S6 mem₀ q) ∧
    ns.map Prod.fst = List.range' lo (hi - lo) ∧
    (∀ q ∈ ns, ∀ (hs : q.1 < cap) (d : DSHist), p4SpanAfter P S6 mem₀ tasks ⟨q.1, hs⟩ = some d →
      q.2.Nodup ∧ q.2.toFinset = (d.state P).G.E) ∧
    Phase4WSAt st'.mem hp eCap
      { (p4SpanWV P S6 mem₀ OS v tasks qs ns).1 with delSup := Ld, insSup := Li, reemb := Lr } ∧
    (∀ e, e ∈ Ld ↔ e ∈ (p4SpanWV P S6 mem₀ OS v tasks qs ns).1.delSup ∨ e ∈ batchDeletes U) ∧
    (∀ e, e ∈ Li ↔ e ∈ (p4SpanWV P S6 mem₀ OS v tasks qs ns).1.insSup ∨ e ∈ batchDeletes U ∨
      e ∈ batchInsEdges U ∨ (∃ i : Fin nNew, e ∈ lazyE i) ∨ e ∈ c.fDel) ∧
    (∀ e, e ∈ Lr ↔ e ∈ (p4SpanWV P S6 mem₀ OS v tasks qs ns).1.reemb ∨
      ∃ i : Fin nNew, e ∈ lazyE i) ∧
    (embRep eCap).rep embH (p4SpanWV P S6 mem₀ OS v tasks qs ns).2 y' st'.mem ∧
    (bucketSpannerRep P cap).rep spanTbl (p4SpanAfter P S6 mem₀ tasks) x' st'.mem ∧
    (∀ e < eCap, st'.mem (h₁ + e) = batchLastOp U e) ∧
    (∀ e < eCap, st'.mem (h₁ + eCap + e) = if e ∈ batchDeletes U then 1 else 0) ∧
    (∀ e < eCap, st'.mem (h₁ + 2 * eCap + e) = if e ∈ c.fDel then 1 else 0) ∧
    hp + p4WsSize eCap ≤ h₁ ∧
    h₁ ≤ hp + p4WsSize eCap + (tasks.map (p4TaskSpace P S6 mem₀)).sum +
      rangeCost (p4NewSpace P (p4SpanAfter P S6 mem₀ tasks)) lo hi ∧
    o.value = h₁ + 3 * eCap ∧
    ZeroFrom st'.mem (h₁ + 3 * eCap) ∧
    (∀ a < hp, ¬ bucketFoot spanTbl x6 a → ¬ embFoot eCap embH y a → st'.mem a = mem₀ a) ∧
    (∀ a, bucketFoot spanTbl x' a → bucketFoot spanTbl x6 a ∨ (hp + p4WsSize eCap ≤ a ∧ a < h₁)) ∧
    (∀ a, embFoot eCap embH y' a → embFoot eCap embH y a ∨ (hp + p4WsSize eCap ≤ a ∧ a < h₁)) ∧
    (∀ a, embFoot eCap embH y' a → ¬ bucketFoot spanTbl x' a) ∧
    cost + specPhi P (p4SpanAfter P S6 mem₀ tasks) ≤
      specPhi P S6 + (tasks.map fun t => p4TaskPay P S6 mem₀ t + 70).sum +
        rangeCost (fun s => p4NewPay P (p4SpanAfter P S6 mem₀ tasks) s + 20) lo hi +
        9 * (hi - lo) + 175 * U.length +
        130 * ((List.finRange nNew).map fun i => (lazyE i).length).sum + 90 * nNew +
        105 * c.fDel.length + 440

end

/-! ## Helpers -/

public section

/-- A call followed by a statement, with the cost bound carried along. -/
theorem p4_runs_seq_callRuns_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ}
    {args : List Expr} {s : Stmt} {st : State} {vs : List ℕ} {body : Stmt} {k T : ℕ}
    {Q : Outcome → State → Prop}
    (hargs : evalArgs w st args = some vs) (hb : p.procs[f]? = some body) {o₁ : Outcome}
    {st₁ : State} {c₁ : ℕ} (h₁ : Runs w p ω body (startState vs st.mem st.pos) o₁ st₁ c₁)
    (hrest : ∃ o st' c₂, Runs w p ω s { st₁ with regs := Function.update st.regs r o₁.value }
      o st' c₂ ∧ Q o st' ∧ (k + argsSize args + c₁ + 2) + c₂ ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call r f args) s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨o, st', c₂, hr₂, hq, hc⟩ := hrest
  exact ⟨o, st', (argsSize args + c₁ + 1) + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨_, _, c₂,
    runs_call_iff.mpr ⟨vs, body, o₁, st₁, c₁, hargs, hb, h₁, rfl, rfl, rfl⟩, hr₂, rfl⟩), hq,
    by omega⟩

/-- The descriptors of the tasks stay valid at a larger heap pointer. -/
theorem asmFirstBunStepOut_mono {P : DSParams} {cap : ℕ} {S6 : BucketSpannerState cap}
    {descPtr h h' : ℕ} {tasks : List SpanUpdTask} {mem : ℕ → ℕ}
    (hB : AsmFirstBunStepOut P cap S6 descPtr h tasks mem) (hle : h ≤ h') :
    AsmFirstBunStepOut P cap S6 descPtr h' tasks mem := by
  refine ⟨hB.htasks, hB.hnd, le_trans hB.hdesc_le hle, fun t ht => ?_⟩
  obtain ⟨hs, d, hd, hpre⟩ := hB.hslots t ht
  exact ⟨hs, d, hd, (p4DSUpdatePre_congr hpre hle fun _ _ => rfl).1⟩

theorem p4Free_of_inCell {L cap : ℕ} {spanTbl : ℕ} {x6 : BucketSpannerMeta L cap}
    {eCap embH : ℕ} {y : EmbConc} {hp a : ℕ} (h : P4InCell spanTbl x6 eCap embH y hp a) :
    P4Free spanTbl x6 eCap embH y hp a :=
  ⟨h.2.1, h.2.2, Or.inl h.1⟩

theorem asmFirstP4FrontStmt_noRand (fSpan fSeed fFlags : ℕ) :
    (asmFirstP4FrontStmt fSpan fSeed fFlags).NoRand := by
  simp [asmFirstP4FrontStmt, Stmt.NoRand]

end

/-- The run of the statement from the runs of its three calls. -/
private theorem asmFirstP4Front_run_of {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {fSpan fSeed fFlags : ℕ} {bSpan bSeed bFlags : Stmt}
    (hfSpan : p.procs[fSpan]? = some bSpan) (hfSeed : p.procs[fSeed]? = some bSeed)
    (hfFlags : p.procs[fFlags]? = some bFlags)
    {spanTbl descPtr n hp eCap oldS embH lo hi batch chg lazyPtr nNew pos : ℕ} {mem₀ : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hsz : hp + (11 * eCap + 4) < 2 ^ w)
    {o₁ o₂ o₃ : Outcome} {st₁ st₂ st₃ : State} {c₁ c₂ c₃ : ℕ}
    (h₁ : Runs w p ω bSpan (startState [spanTbl, descPtr, n, hp + (11 * eCap + 4), hp, eCap, oldS,
      embH, lo, hi] mem₀ pos) o₁ st₁ c₁)
    (h₂ : Runs w p ω bSeed (startState [batch, chg, hp, eCap, lazyPtr, nNew] st₁.mem st₁.pos)
      o₂ st₂ c₂)
    (h₃ : Runs w p ω bFlags (startState [batch, chg, eCap, o₁.value] st₂.mem st₂.pos) o₃ st₃ c₃) :
    ∃ st' c, Runs w p ω (asmFirstP4FrontStmt fSpan fSeed fFlags)
        (startState [spanTbl, descPtr, n, hp, eCap, oldS, embH, lo, hi, batch, chg, lazyPtr, nNew]
          mem₀ pos) (.returned o₃.value) st' c ∧ st'.mem = st₃.mem ∧ c ≤ c₁ + c₂ + c₃ + 100 := by
  have key : ∃ o st' c, Runs w p ω (asmFirstP4FrontStmt fSpan fSeed fFlags)
      (startState [spanTbl, descPtr, n, hp, eCap, oldS, embH, lo, hi, batch, chg, lazyPtr, nNew]
        mem₀ pos) o st' c ∧ (o = .returned o₃.value ∧ st'.mem = st₃.mem) ∧
      0 + c ≤ c₁ + c₂ + c₃ + 100 := by
    unfold asmFirstP4FrontStmt
    refine runs_seq_assign_le (v := hp + (11 * eCap + 4)) ?_ ?_
    · exact Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
        (Expr.eval_add (Expr.eval_mul (Expr.eval_const (by omega))
          (Expr.eval_reg_of_eq (by simp [startState])) (by omega)) (Expr.eval_const (by omega))
          (by omega)) hsz
    refine p4_runs_seq_callRuns_le (by eval_expr) hfSpan h₁ ?_
    refine p4_runs_seq_callRuns_le (by eval_expr) hfSeed h₂ ?_
    refine p4_runs_seq_callRuns_le (by eval_expr) hfFlags h₃ ?_
    wram_step
    · exact ⟨by simp, rfl⟩
    · wram_cost
  obtain ⟨o, st', c, hr, ⟨rfl, hm⟩, hc⟩ := key
  exact ⟨st', c, hr, hm, by omega⟩

/-- A change record depends only on its own `c.words` cells. -/
private theorem p4LsfChangeAt_of_agree {mem₁ mem₂ : ℕ → ℕ} {a : ℕ} {c : LSFChange}
    (hC : LSFChangeAt mem₁ a c) (h : ∀ x, a ≤ x → x < a + c.words → mem₂ x = mem₁ x) :
    LSFChangeAt mem₂ a c := by
  obtain ⟨h0, hr, h1, hf⟩ := hC
  have hw : c.words = 2 + (c.roots.length + c.fDel.length) := rfl
  refine ⟨?_, fun k hk => ?_, ?_, fun k hk => ?_⟩
  · rw [h a le_rfl (by omega)]; exact h0
  · rw [h _ (by omega) (by omega)]; exact hr k hk
  · rw [h _ (by omega) (by omega)]; exact h1
  · rw [h _ (by omega) (by omega)]; exact hf k hk

public section

set_option maxHeartbeats 1600000 in
/-- **The run of the front of Phase 4.** The memory from `hp` on is zero, so the workspace at `hp`
starts empty. The hypotheses of the spanner part (`asmFirstP4Span_runs`) are asked with the
workspace at `hp` and the heap pointer `hp + p4WsSize eCap`; the cells it reads below `hp` are
`P4InCell`. The batch, the table of the lists of the newly active components with these lists,
and the change record are `P4InCell` too. Then `asmFirstP4FrontStmt` ends in `P4FrontPost`. -/
theorem asmFirstP4Front_runs {P : DSParams} {cap : ℕ}
    {fSpan fSeed fFlags fSeedB fSeedL fAppend fLoop fNewLoop fNew bSpan fTask fAfter : ℕ}
    {fScanUH fScanD fScanR fDleft fCopy fEdge fPush fMark fScanNew bRead bCopy : ℕ}
    {p : Program}
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
    {OS : Finset ℕ} {v : EmbView} {y : EmbConc} {G₀ : MGraph} {U : List Update}
    {c : LSFChange} {lazyE : Fin nNew → List ℕ} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ P.w)
    (hBun : AsmFirstBunStepOut P cap S6 descPtr hp tasks mem₀)
    (hS6 : (bucketSpannerRep P cap).rep spanTbl S6 x6 mem₀)
    (hEmb : (embRep eCap).rep embH v y mem₀)
    (hOS : ∀ e < eCap, mem₀ (oldS + e) = if e ∈ OS then 1 else 0)
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
      rangeCost (p4NewSpace P (p4SpanAfter P S6 mem₀ tasks)) lo hi + 3 * eCap < 2 ^ P.w) :
    ∃ o st' cost, Runs P.w p ω (asmFirstP4FrontStmt fSpan fSeed fFlags)
        (startState [spanTbl, descPtr, tasks.length, hp, eCap, oldS, embH, lo, hi, batch, chg,
          lazyPtr, nNew] mem₀ pos) o st' cost ∧
      P4FrontPost P S6 x6 spanTbl hp eCap embH OS v y tasks lo hi U c lazyE mem₀ o st' cost := by
  classical
  have hsz : p4WsSize eCap = 11 * eCap + 4 := rfl
  -- The spanner part, with the empty workspace at `hp`.
  obtain ⟨o₁, st₁, c₁, hr₁, qs, ns, x₁, y₁, hqs, hqsOK, hns, hnsOK, hW₁, hEmb₁, hS₁, hlo₁, hhi₁,
    hz₁, hfr₁, hbf₁, hef₁, hdj₁, hc₁⟩ :=
    asmFirstP4Span_runs (pos := pos) (ω := ω) (OS := OS) (S := ⟨∅, ∅, ∅, [], [], [], ∅, []⟩)
      (ws := hp) (hp₀ := hp + p4WsSize eCap) hfLoop hfNewLoop hpS hfTask hfAfter hfUH hfD hfR
      hfDl hfC hfEdge hfPush hfMark hfNew hfN hcopy hread hw16
      (asmFirstBunStepOut_mono hBun (Nat.le_add_right _ _)) (phase4WSAt_zero hz) hS6 hEmb hOS
      (fun e he => ⟨by have := (hoIn e he).1; omega, p4Free_of_inCell (hoIn e he)⟩)
      (fun a h1 h2 => p4Free_of_inCell (hdescIn a h1 h2))
      (fun t ht a h1 h2 => p4Free_of_inCell (hbatchIn t ht a h1 h2))
      hcaps hlo hhiW hslots heCap le_rfl
      (fun a ha => by have := hfoot a ha; omega) (fun a ha => by have := hEmbF a ha; omega)
      (fun a ha => Or.inl (hfoot a ha)) (fun a ha => Or.inl (hEmbF a ha)) hDisj
      (Or.inl hoLe) (by omega) (fun a ha => hz a (by omega)) (by omega)
  have hag₁ : ∀ a, P4InCell spanTbl x6 eCap embH y hp a → st₁.mem a = mem₀ a := fun a ha =>
    hfr₁ a (by have := ha.1; omega) (p4Free_of_inCell ha)
  -- The seeds, on the memory after the spanner part.
  have hBat₁ : BatchAt st₁.mem batch G₀ U words :=
    BatchAt.of_agree hBat fun i hi => hag₁ _ (hBatIn _ (by omega) (by omega))
  have hChg₁ : LSFChangeAt st₁.mem chg c :=
    p4LsfChangeAt_of_agree hChg fun x h1 h2 => hag₁ x (hChgIn x h1 h2)
  have hLazy₁ : ∀ (i : Fin nNew), ∃ ptr, st₁.mem (lazyPtr + 2 * i.1) = ptr ∧
      st₁.mem (lazyPtr + 2 * i.1 + 1) = (lazyE i).length ∧ ListAt st₁.mem ptr (lazyE i) ∧
      ptr + (lazyE i).length < 2 ^ P.w ∧ (∀ e ∈ lazyE i, e < eCap) ∧
      (ptr + (lazyE i).length ≤ hp ∨ hp + p4WsSize eCap ≤ ptr) := by
    intro i
    obtain ⟨ptr, h1, h2, h3, h4, h5, h6⟩ := hLazy i
    have hi := i.2
    exact ⟨ptr, (hag₁ _ (hLazyIn _ (by omega) (by omega))).trans h1,
      (hag₁ _ (hLazyIn _ (by omega) (by omega))).trans h2,
      fun k hk => (hag₁ _ (h6 _ (by omega) (by omega))).trans (h3 k hk), by omega, h5, Or.inl h4⟩
  obtain ⟨st₂, c₂, Ld, Li, Lr, hr₂, hW₂, hLd, hLi, hLr, hfr₂, hc₂⟩ :=
    asmFirstP4Seed_runs (pos := st₁.pos) (ω := ω) hfSeedB hfSeedL hfAppend hfPush hw16 hW₁
      (by omega) hBat₁ hCaps (Or.inl hBat_le) (by omega) hLazy₁ (Or.inl hLazy_le) (by omega)
      hChg₁ hfDel_cap (Or.inl hChg_le) (by omega)
  -- The flags, at the heap pointer after the spanner part.
  have hag₂ : ∀ a, a < hp → st₂.mem a = st₁.mem a := fun a ha => hfr₂ a (Or.inl ha)
  have hBat₂ : BatchAt st₂.mem batch G₀ U words :=
    BatchAt.of_agree hBat₁ fun i hi => hag₂ _ (by omega)
  have hChg₂ : LSFChangeAt st₂.mem chg c :=
    p4LsfChangeAt_of_agree hChg₁ fun x h1 h2 => hag₂ x (by omega)
  have hz₂ : ZeroFrom st₂.mem o₁.value := fun a ha =>
    (hfr₂ a (Or.inr (by omega))).trans (hz₁ a ha)
  obtain ⟨st₃, c₃, hr₃, hLO, hDB, hFD, hz₃, hfr₃, hc₃⟩ :=
    asmFirstPrepFlags_runs (p := p) (pos := st₂.pos) (ω := ω) hw16 hBat₂ (by omega) hCaps hChg₂
      (by omega) hfDel_cap hz₂ (by omega)
  -- The run of the whole statement.
  obtain ⟨st', cost, hrun, hm, hcost⟩ :=
    asmFirstP4Front_run_of (lazyPtr := lazyPtr) (nNew := nNew) hfSpan hfSeed hfFlags hw16
      (by omega) hr₁ hr₂ hr₃
  -- The cells that the seeds and the flags keep.
  have hkeep : ∀ a, (a < hp ∨ hp + p4WsSize eCap ≤ a) → a < o₁.value → st'.mem a = st₁.mem a :=
    fun a h1 h2 => by rw [hm, hfr₃ a h2, hfr₂ a h1]
  refine ⟨_, st', cost, hrun, qs, ns, x₁, y₁, o₁.value, Ld, Li, Lr, hqs, hqsOK, hns, hnsOK,
    phase4WSAt_of_agree hW₂ fun a h1 h2 => by rw [hm, hfr₃ a (by omega)], hLd, hLi, hLr,
    (embRep_local eCap embH _ y₁ st₁.mem st'.mem fun a ha => ?_).1 hEmb₁,
    (bucketSpannerRep_local P cap spanTbl _ x₁ st₁.mem st'.mem fun a ha => ?_).1 hS₁,
    fun e he => by rw [hm]; exact hLO e he, fun e he => by rw [hm]; exact hDB e he,
    fun e he => by rw [hm]; exact hFD e he, hlo₁, hhi₁, rfl, by rw [hm]; exact hz₃,
    fun a ha hb he => ?_, hbf₁, hef₁, hdj₁, ?_⟩
  · rcases hef₁ a ha with h | ⟨h1, h2⟩
    · have := hEmbF a h; exact (hkeep a (Or.inl this) (by omega)).symm
    · exact (hkeep a (Or.inr h1) h2).symm
  · rcases hbf₁ a ha with h | ⟨h1, h2⟩
    · have := hfoot a h; exact (hkeep a (Or.inl this) (by omega)).symm
    · exact (hkeep a (Or.inr h1) h2).symm
  · rw [hkeep a (Or.inl ha) (by omega)]; exact hag₁ a ⟨ha, hb, he⟩
  · omega

end

end MinCostFlow.SparseCore.Program
