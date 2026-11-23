module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4Loop
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4NewLoop

import WordRAM.Tactic

/-!
# The spanner part of Phase 4 (`AssemblyFirstStepP4Span`)

Phase 4 first updates the spanners of the slots that Phase 3 touched, and then reads the spanners
of the slots that Phase 2 made. The procedure `asmFirstP4SpanStmt fLoop fNewLoop`, with arguments
`[spanTbl, descPtr, n, hp, ws, eCap, oldS, embH, lo, hi]`, runs the loop over the tasks
(`asmFirstP4LoopStmt`, `AssemblyFirstStepP4Loop.lean`) and then the loop over the new slots
`lo, …, hi - 1` (`asmFirstP4NewLoopStmt`, `AssemblyFirstStepP4NewLoop.lean`) with the heap pointer
that the first loop returns. It returns the last heap pointer.

`asmFirstP4Span_runs` gives `P4SpanPost`. The new slots read the spanners after the tasks
(`p4SpanAfter`), so the model of the second loop is taken on these spanners.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Read MinCostFlow.SparseCore.Program.Restart

/-! ## The procedure and what it leaves -/

@[expose] public section

/-- **The spanner part of Phase 4**, `[spanTbl, descPtr, n, hp, ws, eCap, oldS, embH, lo, hi]`.
Register `10` holds the heap pointer after each loop. -/
def asmFirstP4SpanStmt (fLoop fNewLoop : ℕ) : Stmt :=
  .call 10 fLoop [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7] ;;
  .call 10 fNewLoop [.reg 0, .reg 4, .reg 5, .reg 7, .reg 8, .reg 9, .reg 10] ;;
  .ret (.reg 10)

/-- What the spanner part of Phase 4 leaves, from the memory `mem₀`, the spanners `S6` (meta
`x6`), the workspace `S` and the embedding table `v` (concrete data `y`). The list `qs` holds the
outputs of the updates of the tasks (`P4OutOK`), and the list `ns` holds the edge lists of the
graphs of the new slots, read in the spanners after the tasks. The memory holds the workspace
and the table after both loops, and the spanners after the tasks. The heap pointer grows by at
most the space of both loops, the free cells below `hp₀` are kept (`P4Free`), the footprints
grow only above `hp₀` and stay apart, and the cost is paid by the potential of the spanners and
the pay of each task and of each new slot. -/
def P4SpanPost (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (x6 : BucketSpannerMeta P.L cap) (spanTbl hp₀ ws eCap embH : ℕ) (OS : Finset ℕ)
    (S : Phase4WS) (v : EmbView) (y : EmbConc) (tasks : List SpanUpdTask) (lo hi : ℕ)
    (mem₀ : ℕ → ℕ) (o : Outcome) (st' : State) (c : ℕ) : Prop :=
  ∃ (qs : List (SpanUpdTask × P4TaskOut)) (ns : List (ℕ × List ℕ))
    (x' : BucketSpannerMeta P.L cap) (y' : EmbConc),
    qs.map Prod.fst = tasks ∧ (∀ q ∈ qs, P4OutOK P S6 mem₀ q) ∧
    ns.map Prod.fst = List.range' lo (hi - lo) ∧
    (∀ q ∈ ns, ∀ (hs : q.1 < cap) (d : DSHist), p4SpanAfter P S6 mem₀ tasks ⟨q.1, hs⟩ = some d →
      q.2.Nodup ∧ q.2.toFinset = (d.state P).G.E) ∧
    Phase4WSAt st'.mem ws eCap (ns.foldl (p4NewStep P (p4SpanAfter P S6 mem₀ tasks))
      (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v))).1 ∧
    (embRep eCap).rep embH (ns.foldl (p4NewStep P (p4SpanAfter P S6 mem₀ tasks))
      (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v))).2 y' st'.mem ∧
    (bucketSpannerRep P cap).rep spanTbl (p4SpanAfter P S6 mem₀ tasks) x' st'.mem ∧
    hp₀ ≤ o.value ∧
    o.value ≤ hp₀ + (tasks.map (p4TaskSpace P S6 mem₀)).sum +
      rangeCost (p4NewSpace P (p4SpanAfter P S6 mem₀ tasks)) lo hi ∧
    ZeroFrom st'.mem o.value ∧
    (∀ a < hp₀, P4Free spanTbl x6 eCap embH y ws a → st'.mem a = mem₀ a) ∧
    (∀ a, bucketFoot spanTbl x' a → bucketFoot spanTbl x6 a ∨ (hp₀ ≤ a ∧ a < o.value)) ∧
    (∀ a, embFoot eCap embH y' a → embFoot eCap embH y a ∨ (hp₀ ≤ a ∧ a < o.value)) ∧
    (∀ a, embFoot eCap embH y' a → ¬ bucketFoot spanTbl x' a) ∧
    c + specPhi P (p4SpanAfter P S6 mem₀ tasks) ≤
      specPhi P S6 + (tasks.map fun t => p4TaskPay P S6 mem₀ t + 70).sum +
        rangeCost (fun s => p4NewPay P (p4SpanAfter P S6 mem₀ tasks) s + 20) lo hi +
        9 * (hi - lo) + 60

end

public section

theorem asmFirstP4SpanStmt_noRand (fLoop fNewLoop : ℕ) :
    (asmFirstP4SpanStmt fLoop fNewLoop).NoRand := by
  simp [asmFirstP4SpanStmt, Stmt.NoRand]

set_option maxHeartbeats 1600000 in
/-- **The run of the spanner part of Phase 4.** The hypotheses are those of
`asmFirstP4Loop_runs` and of `asmFirstP4NewLoop_runs`. The facts on the new slots are asked of
the spanners after the tasks, and the room is asked for both loops together. Then
`asmFirstP4SpanStmt` ends in `P4SpanPost`. -/
theorem asmFirstP4Span_runs {P : DSParams} {cap : ℕ} {fLoop fNewLoop fNew bSpan fTask fAfter : ℕ}
    {fScanUH fScanD fScanR fDleft fCopy fEdge fPush fMark fScanNew bRead bCopy : ℕ}
    {p : Program}
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
    {spanTbl descPtr hp₀ ws eCap oldS embH lo hi pos : ℕ} {S6 : BucketSpannerState cap}
    {x6 : BucketSpannerMeta P.L cap} {tasks : List SpanUpdTask} {OS : Finset ℕ} {S : Phase4WS}
    {v : EmbView} {y : EmbConc} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ P.w)
    (hBun : AsmFirstBunStepOut P cap S6 descPtr hp₀ tasks mem₀)
    (hW : Phase4WSAt mem₀ ws eCap S)
    (hS6 : (bucketSpannerRep P cap).rep spanTbl S6 x6 mem₀)
    (hEmb : (embRep eCap).rep embH v y mem₀)
    (hOS : ∀ e < eCap, mem₀ (oldS + e) = if e ∈ OS then 1 else 0)
    (hoFree : ∀ e < eCap, oldS + e < hp₀ ∧ P4Free spanTbl x6 eCap embH y ws (oldS + e))
    (hdescFree : ∀ a, descPtr ≤ a → a < descPtr + 3 * tasks.length →
      P4Free spanTbl x6 eCap embH y ws a)
    (hbatchFree : ∀ t ∈ tasks, ∀ a, t.batchPtr ≤ a → a < t.batchPtr + t.W →
      P4Free spanTbl x6 eCap embH y ws a)
    (hcaps : ∀ t ∈ tasks, ∀ (hs : t.slot < cap) (d : DSHist), S6 ⟨t.slot, hs⟩ = some d →
      mem₀ t.batchPtr ≠ 0 → P4TaskCaps P eCap d (decodeBatch mem₀ t.batchPtr (d.state P).G).1)
    (hlo : lo ≤ hi) (hhiW : hi < 2 ^ P.w)
    (hslots : ∀ s, lo ≤ s → s < hi → ∃ (hs : s < cap) (d : DSHist),
      p4SpanAfter P S6 mem₀ tasks ⟨s, hs⟩ = some d ∧ ∀ e ∈ (d.state P).G.E, e < eCap)
    (heCap : eCap ≤ P.eCap)
    (hWsH : ws + p4WsSize eCap ≤ hp₀)
    (hfoot : ∀ a, bucketFoot spanTbl x6 a → a < hp₀)
    (hEmbF : ∀ a, embFoot eCap embH y a → a < hp₀)
    (hSpanWs : ∀ a, bucketFoot spanTbl x6 a → a < ws ∨ ws + p4WsSize eCap ≤ a)
    (hEmbWs : ∀ a, embFoot eCap embH y a → a < ws ∨ ws + p4WsSize eCap ≤ a)
    (hDisj : ∀ a, embFoot eCap embH y a → ¬ bucketFoot spanTbl x6 a)
    (ho_disj : oldS + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ oldS) (ho_w : oldS + eCap < 2 ^ P.w)
    (hz : ZeroFrom mem₀ hp₀)
    (hspace : hp₀ + (tasks.map (p4TaskSpace P S6 mem₀)).sum +
      rangeCost (p4NewSpace P (p4SpanAfter P S6 mem₀ tasks)) lo hi < 2 ^ P.w) :
    ∃ o st' c, Runs P.w p ω (asmFirstP4SpanStmt fLoop fNewLoop)
        (startState [spanTbl, descPtr, tasks.length, hp₀, ws, eCap, oldS, embH, lo, hi] mem₀ pos)
        o st' c ∧
      P4SpanPost P S6 x6 spanTbl hp₀ ws eCap embH OS S v y tasks lo hi mem₀ o st' c := by
  classical
  set st₀ := startState [spanTbl, descPtr, tasks.length, hp₀, ws, eCap, oldS, embH, lo, hi]
    mem₀ pos with hst₀
  have r0 : st₀.regs 0 = spanTbl := by simp [hst₀, startState]
  have r1 : st₀.regs 1 = descPtr := by simp [hst₀, startState]
  have r2 : st₀.regs 2 = tasks.length := by simp [hst₀, startState]
  have r3 : st₀.regs 3 = hp₀ := by simp [hst₀, startState]
  have r4 : st₀.regs 4 = ws := by simp [hst₀, startState]
  have r5 : st₀.regs 5 = eCap := by simp [hst₀, startState]
  have r6 : st₀.regs 6 = oldS := by simp [hst₀, startState]
  have r7 : st₀.regs 7 = embH := by simp [hst₀, startState]
  have r8 : st₀.regs 8 = lo := by simp [hst₀, startState]
  have r9 : st₀.regs 9 = hi := by simp [hst₀, startState]
  -- The loop over the tasks.
  obtain ⟨o₁, st₁, c₁, hrun₁, hpost₁⟩ := asmFirstP4Loop_runs (pos := pos) (ω := ω) (OS := OS)
    (S := S) hpS hfTask hfAfter hfUH hfD hfR hfDl hfC hfEdge hfPush hfMark hcopy hread hw16 hBun
    hW hS6 hEmb hOS hoFree hdescFree hbatchFree hcaps heCap hWsH hfoot hEmbF hSpanWs hEmbWs hDisj
    ho_disj ho_w hz (by omega)
  obtain ⟨qs, x₁, y₁, hqs, hqsOK, hW₁, hEmb₁, hS₁, hlo₁, hhi₁, hz₁, hfr₁, hbf₁, hef₁, hdj₁,
    hc₁⟩ := hpost₁
  have hargs₁ : evalArgs P.w st₀ [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7] =
      some [spanTbl, descPtr, tasks.length, hp₀, ws, eCap, oldS, embH] :=
    evalArgs_cons (Expr.eval_reg_of_eq r0) <| evalArgs_cons (Expr.eval_reg_of_eq r1) <|
    evalArgs_cons (Expr.eval_reg_of_eq r2) <| evalArgs_cons (Expr.eval_reg_of_eq r3) <|
    evalArgs_cons (Expr.eval_reg_of_eq r4) <| evalArgs_cons (Expr.eval_reg_of_eq r5) <|
    evalArgs_cons (Expr.eval_reg_of_eq r6) <| evalArgs_cons (Expr.eval_reg_of_eq r7) <|
    evalArgs_nil _ _
  have hcall₁ : Runs P.w p ω
      (.call 10 fLoop [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7]) st₀ .normal
      ⟨st₁.mem, Function.update st₀.regs 10 o₁.value, st₁.pos⟩
      (argsSize [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7] + c₁ + 1) :=
    runs_call_iff.mpr ⟨_, _, o₁, st₁, c₁, hargs₁, hfLoop, hrun₁, rfl, rfl, rfl⟩
  -- The loop over the new slots, on the spanners after the tasks.
  have hbf₁' : ∀ a, bucketFoot spanTbl x₁ a → a < o₁.value := fun a ha => by
    rcases hbf₁ a ha with h | ⟨-, h⟩
    · have := hfoot a h; omega
    · exact h
  have hef₁' : ∀ a, embFoot eCap embH y₁ a → a < o₁.value := fun a ha => by
    rcases hef₁ a ha with h | ⟨-, h⟩
    · have := hEmbF a h; omega
    · exact h
  have hbw₁ : ∀ a, bucketFoot spanTbl x₁ a → a < ws ∨ ws + p4WsSize eCap ≤ a := fun a ha => by
    rcases hbf₁ a ha with h | ⟨h, -⟩
    · exact hSpanWs a h
    · right; omega
  have hew₁ : ∀ a, embFoot eCap embH y₁ a → a < ws ∨ ws + p4WsSize eCap ≤ a := fun a ha => by
    rcases hef₁ a ha with h | ⟨h, -⟩
    · exact hEmbWs a h
    · right; omega
  obtain ⟨o₂, st₂, c₂, hrun₂, ns, y₂, hns, hnsOK, hW₂, hEmb₂, hS₂, hlo₂, hhi₂, hz₂, hfr₂, hef₂,
    hdj₂, hc₂⟩ := asmFirstP4NewLoop_runs (pos := st₁.pos) (ω := ω)
      (S := (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v)).1)
      (v := (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v)).2) (y := y₁)
      hfNew hfN hfC hfPush hcopy hread hw16 hlo hhiW hslots hW₁ hS₁ hEmb₁ heCap (by omega)
      hbf₁' hef₁' hbw₁ hew₁ hdj₁ hz₁ (by omega)
  set R₁ := Function.update st₀.regs 10 o₁.value with hR₁
  have hargs₂ : evalArgs P.w ⟨st₁.mem, R₁, st₁.pos⟩
      [.reg 0, .reg 4, .reg 5, .reg 7, .reg 8, .reg 9, .reg 10] =
      some [spanTbl, ws, eCap, embH, lo, hi, o₁.value] :=
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [hR₁, r0])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [hR₁, r4])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [hR₁, r5])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [hR₁, r7])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [hR₁, r8])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [hR₁, r9])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [hR₁])) <| evalArgs_nil _ _
  have hcall₂ : Runs P.w p ω
      (.call 10 fNewLoop [.reg 0, .reg 4, .reg 5, .reg 7, .reg 8, .reg 9, .reg 10])
      ⟨st₁.mem, R₁, st₁.pos⟩ .normal ⟨st₂.mem, Function.update R₁ 10 o₂.value, st₂.pos⟩
      (argsSize [.reg 0, .reg 4, .reg 5, .reg 7, .reg 8, .reg 9, .reg 10] + c₂ + 1) :=
    runs_call_iff.mpr ⟨_, _, o₂, st₂, c₂, hargs₂, hfNewLoop, hrun₂, rfl, rfl, rfl⟩
  set st₃ : State := ⟨st₂.mem, Function.update R₁ 10 o₂.value, st₂.pos⟩ with hst₃
  have hret : Runs P.w p ω (.ret (.reg 10)) st₃ (.returned o₂.value) st₃ ((Expr.reg 10).size + 1) :=
    runs_ret_iff.mpr ⟨o₂.value, Expr.eval_reg_of_eq (by simp [hst₃]), rfl, rfl, rfl⟩
  have hrun : Runs P.w p ω (asmFirstP4SpanStmt fLoop fNewLoop) st₀ (.returned o₂.value) st₃
      ((argsSize [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7] + c₁ + 1) +
        ((argsSize [.reg 0, .reg 4, .reg 5, .reg 7, .reg 8, .reg 9, .reg 10] + c₂ + 1) +
          ((Expr.reg 10).size + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcall₁, runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcall₂, hret,
      rfl⟩), rfl⟩)
  refine ⟨.returned o₂.value, st₃, _, hrun, qs, ns, x₁, y₂, hqs, hqsOK, hns, hnsOK, hW₂, hEmb₂,
    hS₂, by show hp₀ ≤ o₂.value; omega, by show o₂.value ≤ _; omega, hz₂, fun a ha hfa => ?_,
    fun a ha => ?_, fun a ha => ?_, hdj₂, ?_⟩
  · -- The free cells below `hp₀` are outside the footprints after the tasks.
    have hb : ¬ bucketFoot spanTbl x₁ a := fun hb => by
      rcases hbf₁ a hb with h | ⟨h, -⟩
      · exact hfa.1 h
      · omega
    have he : ¬ embFoot eCap embH y₁ a := fun he => by
      rcases hef₁ a he with h | ⟨h, -⟩
      · exact hfa.2.1 h
      · omega
    show st₂.mem a = mem₀ a
    rw [hfr₂ a (by omega) ⟨hb, he, hfa.2.2⟩, hfr₁ a ha hfa]
  · show bucketFoot spanTbl x6 a ∨ (hp₀ ≤ a ∧ a < o₂.value)
    rcases hbf₁ a ha with h | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, by omega⟩
  · show embFoot eCap embH y a ∨ (hp₀ ≤ a ∧ a < o₂.value)
    rcases hef₂ a ha with h | ⟨h, h'⟩
    · rcases hef₁ a h with h | ⟨h, h'⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, by omega⟩
    · exact Or.inr ⟨by omega, h'⟩
  · simp only [argsSize, Expr.size] at hc₂ ⊢
    omega

end

end MinCostFlow.SparseCore.Program
