module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4LoopDefs

import WordRAM.Tactic

/-!
# The loop over the tasks of Phase 4 (`AssemblyFirstStepP4Loop`)

Phase 3 leaves the descriptors `[slot, batchPtr, W]` of the tasks at `descPtr`
(`AsmFirstBunStepOut`). The loop `asmFirstP4LoopStmt fTask`, with arguments
`[spanTbl, descPtr, n, hp, ws, eCap, oldS, embH]`, reads each descriptor and runs its task
(`asmFirstP4TaskStmt`, `AssemblyFirstStepP4Task.lean`) with the current heap pointer. It returns
the last heap pointer.

`asmFirstP4Loop_runs` says what the loop leaves (`P4LoopPost`): the spanners after the tasks
(`p4SpanAfter`), the workspace and the embedding table after the tasks (`p4WVStep`, with the
outputs of the updates in a list `qs` whose facts are `P4OutOK`), the heap pointer, the frame,
the footprints, and the cost against the potential of the spanners.

The slots of the tasks are distinct (`AsmFirstBunStepOut.hnd`). So when task `i` runs, its slot
still holds the history it had at the start (`p4SpanAfter_unchanged`), and the facts that Phase 3
gives about this history (`DSUpdatePre`) apply. The batch of the task is not changed by the
earlier tasks, since it lies outside every footprint and outside the workspace. So the batch
reads the same, and `DSUpdatePre` holds at the current heap pointer (`p4DSUpdatePre_congr`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Read MinCostFlow.SparseCore.Program.Restart

/-! ## The procedure and what it leaves -/

@[expose] public section

/-- The body of the loop: it reads descriptor `i` (`slot`, `batchPtr`, `W`) into registers
`9`, `10`, `11` and runs its task with the heap pointer of register `3`, which then gets the new
heap pointer. Registers: `0 = spanTbl`, `1 = descPtr`, `2 = n`, `3 = hp`, `4 = ws`, `5 = eCap`,
`6 = oldS`, `7 = embH`, `8 = i`. -/
def asmFirstP4LoopBody (fTask : ℕ) : Stmt :=
  .assign 9 (.load (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 8)))) ;;
  .assign 10 (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 8))) (.const 1))) ;;
  .assign 11 (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 8))) (.const 2))) ;;
  .call 3 fTask [.reg 0, .reg 9, .reg 10, .reg 11, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7]

/-- **The loop over the tasks of Phase 4**, `[spanTbl, descPtr, n, hp, ws, eCap, oldS, embH]`.
It returns the last heap pointer. -/
def asmFirstP4LoopStmt (fTask : ℕ) : Stmt :=
  forRange 8 (.const 0) (.reg 2) (asmFirstP4LoopBody fTask) ;;
  .ret (.reg 3)

/-- What the loop over `tasks` leaves, from the memory `mem₀`, the spanners `S6` (meta `x6`), the
workspace `S` and the embedding table `v` (concrete data `y`). There are outputs `qs` of the
updates, one entry per task, with the facts `P4OutOK`, and metas `x'` and `y'` such that the
memory holds the workspace and the table after the tasks (`p4WVStep`) and the spanners after the
tasks (`p4SpanAfter`). The returned heap pointer grows by at most the space of the tasks. The
loop keeps the free cells below `hp₀` (`P4Free`), the footprints grow only above `hp₀`, and they
stay apart. The cost and the potential of the spanners are paid by `p4TaskPay` of each task. -/
def P4LoopPost (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (x6 : BucketSpannerMeta P.L cap) (spanTbl hp₀ ws eCap embH : ℕ) (OS : Finset ℕ)
    (S : Phase4WS) (v : EmbView) (y : EmbConc) (tasks : List SpanUpdTask) (mem₀ : ℕ → ℕ)
    (o : Outcome) (st' : State) (c : ℕ) : Prop :=
  ∃ (qs : List (SpanUpdTask × P4TaskOut)) (x' : BucketSpannerMeta P.L cap) (y' : EmbConc),
    qs.map Prod.fst = tasks ∧ (∀ q ∈ qs, P4OutOK P S6 mem₀ q) ∧
    Phase4WSAt st'.mem ws eCap (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v)).1 ∧
    (embRep eCap).rep embH (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v)).2 y' st'.mem ∧
    (bucketSpannerRep P cap).rep spanTbl (p4SpanAfter P S6 mem₀ tasks) x' st'.mem ∧
    hp₀ ≤ o.value ∧ o.value ≤ hp₀ + (tasks.map (p4TaskSpace P S6 mem₀)).sum ∧
    ZeroFrom st'.mem o.value ∧
    (∀ a < hp₀, P4Free spanTbl x6 eCap embH y ws a → st'.mem a = mem₀ a) ∧
    (∀ a, bucketFoot spanTbl x' a → bucketFoot spanTbl x6 a ∨ (hp₀ ≤ a ∧ a < o.value)) ∧
    (∀ a, embFoot eCap embH y' a → embFoot eCap embH y a ∨ (hp₀ ≤ a ∧ a < o.value)) ∧
    (∀ a, embFoot eCap embH y' a → ¬ bucketFoot spanTbl x' a) ∧
    c + specPhi P (p4SpanAfter P S6 mem₀ tasks) ≤
      specPhi P S6 + (tasks.map fun t => p4TaskPay P S6 mem₀ t + 70).sum + 20

end

public section

theorem asmFirstP4LoopStmt_noRand (fTask : ℕ) : (asmFirstP4LoopStmt fTask).NoRand := by
  simp [asmFirstP4LoopStmt, asmFirstP4LoopBody, forRange, forUp, Stmt.NoRand]

end

/-! ## The invariant of the loop -/

/-- The invariant after `i` tasks, on the registers `R` and the memory `mem`. -/
private def P4LoopInvAt (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (x6 : BucketSpannerMeta P.L cap) (spanTbl descPtr hp₀ ws eCap oldS embH : ℕ)
    (OS : Finset ℕ) (S : Phase4WS) (v : EmbView) (y : EmbConc) (tasks : List SpanUpdTask)
    (mem₀ : ℕ → ℕ) (i : ℕ) (R mem : ℕ → ℕ) : Prop :=
  R 0 = spanTbl ∧ R 1 = descPtr ∧ R 2 = tasks.length ∧ R 4 = ws ∧ R 5 = eCap ∧ R 6 = oldS ∧
  R 7 = embH ∧ R 8 = i ∧
  hp₀ ≤ R 3 ∧ R 3 ≤ hp₀ + ((tasks.take i).map (p4TaskSpace P S6 mem₀)).sum ∧
  ZeroFrom mem (R 3) ∧
  (∀ a < hp₀, P4Free spanTbl x6 eCap embH y ws a → mem a = mem₀ a) ∧
  (∀ j < i, specPhi P (p4SpanAfter P S6 mem₀ (tasks.take (j + 1))) ≤
    p4TaskPay P S6 mem₀ (tasks.getD j ⟨0, 0, 0⟩) +
      specPhi P (p4SpanAfter P S6 mem₀ (tasks.take j))) ∧
  ∃ (qs : List (SpanUpdTask × P4TaskOut)) (x' : BucketSpannerMeta P.L cap) (y' : EmbConc),
    qs.map Prod.fst = tasks.take i ∧ (∀ q ∈ qs, P4OutOK P S6 mem₀ q) ∧
    Phase4WSAt mem ws eCap (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v)).1 ∧
    (embRep eCap).rep embH (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v)).2 y' mem ∧
    (bucketSpannerRep P cap).rep spanTbl (p4SpanAfter P S6 mem₀ (tasks.take i)) x' mem ∧
    (∀ a, bucketFoot spanTbl x' a → bucketFoot spanTbl x6 a ∨ (hp₀ ≤ a ∧ a < R 3)) ∧
    (∀ a, embFoot eCap embH y' a → embFoot eCap embH y a ∨ (hp₀ ≤ a ∧ a < R 3)) ∧
    (∀ a, embFoot eCap embH y' a → ¬ bucketFoot spanTbl x' a)

/-- The invariant after `i` tasks, on the state `st`. -/
private def P4LoopInv (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (x6 : BucketSpannerMeta P.L cap) (spanTbl descPtr hp₀ ws eCap oldS embH : ℕ)
    (OS : Finset ℕ) (S : Phase4WS) (v : EmbView) (y : EmbConc) (tasks : List SpanUpdTask)
    (mem₀ : ℕ → ℕ) (i : ℕ) (st : State) : Prop :=
  P4LoopInvAt P S6 x6 spanTbl descPtr hp₀ ws eCap oldS embH OS S v y tasks mem₀ i st.regs st.mem

/-- The bound on the cost of round `i`: what its task may pay, plus the drop of the potential of
the spanners, plus `60` for reading the descriptor and the call. -/
private noncomputable def p4LoopStepCost (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) (tasks : List SpanUpdTask) (i : ℕ) : ℕ :=
  60 + (p4TaskPay P S6 mem₀ (tasks.getD i ⟨0, 0, 0⟩) +
    specPhi P (p4SpanAfter P S6 mem₀ (tasks.take i)) -
    specPhi P (p4SpanAfter P S6 mem₀ (tasks.take (i + 1))))

private theorem sum_take_succ (f : SpanUpdTask → ℕ) {tasks : List SpanUpdTask} {i : ℕ}
    (hi : i < tasks.length) :
    ((tasks.take (i + 1)).map f).sum = ((tasks.take i).map f).sum + f (tasks[i]'hi) := by
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append, List.map_singleton,
    List.sum_singleton]

private theorem sum_take_le (f : SpanUpdTask → ℕ) (tasks : List SpanUpdTask) (k : ℕ) :
    ((tasks.take k).map f).sum ≤ (tasks.map f).sum := by
  have h : ((tasks.take k).map f).sum + ((tasks.drop k).map f).sum = (tasks.map f).sum := by
    rw [← List.sum_append, ← List.map_append, List.take_append_drop]
  omega

/-- The slot of task `i` is not the slot of an earlier task, since the slots are distinct. -/
private theorem slot_not_mem_take {tasks : List SpanUpdTask}
    (hnd : (tasks.map SpanUpdTask.slot).Nodup) {i : ℕ} (hi : i < tasks.length) :
    (tasks[i]'hi).slot ∉ (tasks.take i).map SpanUpdTask.slot := by
  intro hm
  rw [List.mem_map] at hm
  obtain ⟨t', ht', heq⟩ := hm
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ht'
  rw [List.length_take] at hk
  have hklen : k < tasks.length := by omega
  have hget : (tasks.take i)[k]'(by rw [List.length_take]; omega) = tasks[k]'hklen :=
    List.getElem_take
  rw [hget] at heq
  have hidx : k = i := (List.Nodup.getElem_inj_iff hnd (i := k) (j := i)
    (hi := by simp [hklen]) (hj := by simp [hi])).mp (by simpa using heq)
  omega

/-! ## The run of the loop -/

public section

set_option maxHeartbeats 4000000 in
/-- **The run of the loop over the tasks of Phase 4.** Phase 3 leaves the descriptors of the
tasks (`AsmFirstBunStepOut`, with heap pointer `hp₀`). The spanners, the embedding table, the
workspace and the presence array `oldS` of the old output graph lie below `hp₀`, and the
spanners, the table and the workspace are apart. The descriptors, the batches and the array
`oldS` are free cells (`P4Free`). For each task that updates its slot, the outputs of the update
and the walks of the new spanner have their edges below `eCap` (`P4TaskCaps`), and there is room
for all tasks. Then `asmFirstP4LoopStmt` ends in `P4LoopPost`. -/
theorem asmFirstP4Loop_runs {P : DSParams} {cap : ℕ} {bSpan fTask fAfter : ℕ}
    {fScanUH fScanD fScanR fDleft fCopy fEdge fPush fMark bRead bCopy : ℕ} {p : Program}
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
    (hcopy : p.HasAt bCopy [copyWords]) (hread : p.HasAt bRead spanReadoutProcs)
    {spanTbl descPtr hp₀ ws eCap oldS embH pos : ℕ} {S6 : BucketSpannerState cap}
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
    (heCap : eCap ≤ P.eCap)
    (hWsH : ws + p4WsSize eCap ≤ hp₀)
    (hfoot : ∀ a, bucketFoot spanTbl x6 a → a < hp₀)
    (hEmbF : ∀ a, embFoot eCap embH y a → a < hp₀)
    (hSpanWs : ∀ a, bucketFoot spanTbl x6 a → a < ws ∨ ws + p4WsSize eCap ≤ a)
    (hEmbWs : ∀ a, embFoot eCap embH y a → a < ws ∨ ws + p4WsSize eCap ≤ a)
    (hDisj : ∀ a, embFoot eCap embH y a → ¬ bucketFoot spanTbl x6 a)
    (ho_disj : oldS + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ oldS) (ho_w : oldS + eCap < 2 ^ P.w)
    (hz : ZeroFrom mem₀ hp₀)
    (hspace : hp₀ + (tasks.map (p4TaskSpace P S6 mem₀)).sum < 2 ^ P.w) :
    ∃ o st' c, Runs P.w p ω (asmFirstP4LoopStmt fTask)
        (startState [spanTbl, descPtr, tasks.length, hp₀, ws, eCap, oldS, embH] mem₀ pos)
        o st' c ∧
      P4LoopPost P S6 x6 spanTbl hp₀ ws eCap embH OS S v y tasks mem₀ o st' c := by
  classical
  have hw1 : 1 < 2 ^ P.w := by omega
  have hdesc_le := hBun.hdesc_le
  have hn_lt : tasks.length < 2 ^ P.w := by omega
  -- One round of the loop.
  have hbody : ∀ i < tasks.length,
      Triple P.w p (P4LoopInv P S6 x6 spanTbl descPtr hp₀ ws eCap oldS embH OS S v y tasks mem₀ i)
        (asmFirstP4LoopBody fTask)
        (normalPost fun st₁ =>
          P4LoopInv P S6 x6 spanTbl descPtr hp₀ ws eCap oldS embH OS S v y tasks mem₀ (i + 1)
              { st₁ with regs := Function.update st₁.regs 8 (i + 1) } ∧
            st₁.regs 8 = i)
        (fun _ => p4LoopStepCost P S6 mem₀ tasks i) := by
    intro i hi st ω' hInv
    obtain ⟨hr0, hr1, hr2, hr4, hr5, hr6, hr7, hr8, hhp_lo, hhp_hi, hzhp, hfr, hph, qs, xi, yi,
      hqs, hqsOK, hWi, hEmbi, hrepi, hfooti, hembfi, hdisji⟩ := hInv
    obtain ⟨t, ht⟩ : ∃ t, tasks[i]'hi = t := ⟨_, rfl⟩
    have htmem : t ∈ tasks := ht ▸ List.getElem_mem hi
    obtain ⟨hs, d, hdS6, hpre0⟩ := hBun.hslots t htmem
    have hW1 : 0 < t.W := by
      have hpre0' := hpre0
      obtain ⟨_, _, _, _, heq0, -, -, hWeq, -⟩ := hpre0'
      simp only [List.cons.injEq, and_true] at heq0
      obtain ⟨-, -, rfl, -⟩ := heq0
      omega
    have hbp_le : t.batchPtr + t.W ≤ hp₀ := p4DSUpdatePre_batch_le hpre0
    have hdesc_i := hBun.htasks i hi
    rw [ht] at hdesc_i
    have hmem_slot : st.mem (descPtr + 3 * i) = t.slot := by
      rw [hfr _ (by omega) (hdescFree _ (by omega) (by omega))]; exact hdesc_i.1
    have hmem_bp : st.mem (descPtr + 3 * i + 1) = t.batchPtr := by
      rw [hfr _ (by omega) (hdescFree _ (by omega) (by omega))]; exact hdesc_i.2.1
    have hmem_W : st.mem (descPtr + 3 * i + 2) = t.W := by
      rw [hfr _ (by omega) (hdescFree _ (by omega) (by omega))]; exact hdesc_i.2.2
    have hnot := slot_not_mem_take hBun.hnd hi
    rw [ht] at hnot
    have hcur : p4SpanAfter P S6 mem₀ (tasks.take i) ⟨t.slot, hs⟩ = some d := by
      unfold p4SpanAfter
      rw [p4SpanAfter_unchanged P S6 mem₀ (j := ⟨t.slot, hs⟩) hnot S6, hdS6]
    have hbatch_ag : ∀ k < t.W, st.mem (t.batchPtr + k) = mem₀ (t.batchPtr + k) := fun k hk =>
      hfr _ (by omega) (hbatchFree t htmem _ (by omega) (by omega))
    obtain ⟨hpre₁, hdec₁⟩ := p4DSUpdatePre_congr hpre0 hhp_lo hbatch_ag
    have hb_eq : st.mem t.batchPtr = mem₀ t.batchPtr := by simpa using hbatch_ag 0 hW1
    have hopB : (opBatch P d [0, t.batchPtr, t.W, st.regs 3] st.mem).1 =
        (decodeBatch mem₀ t.batchPtr (d.state P).G).1 := by
      simp only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some, hdec₁]
    have hsp_eq : dsUpdateOpSpace P d [0, t.batchPtr, t.W, st.regs 3] st.mem =
        dsUpdateOpSpace P d [0, t.batchPtr, t.W, 0] mem₀ := p4OpSpace_eq_of_decode hdec₁
    have hac_eq : dsUpdateAmortCost P d [0, t.batchPtr, t.W, st.regs 3] st.mem =
        dsUpdateAmortCost P d [0, t.batchPtr, t.W, 0] mem₀ := p4AmortCost_eq_of_decode hdec₁
    have htake : tasks.take (i + 1) = tasks.take i ++ [t] := by
      rw [List.take_succ_eq_append_getElem hi, ht]
    have hSpan_succ : p4SpanAfter P S6 mem₀ (tasks.take (i + 1)) =
        p4SpanStep P S6 mem₀ (p4SpanAfter P S6 mem₀ (tasks.take i)) t := by
      unfold p4SpanAfter; rw [htake, List.foldl_append]; rfl
    have hgetD : tasks.getD i ⟨0, 0, 0⟩ = t := by rw [List.getD_eq_getElem _ _ hi, ht]
    have hspsum := sum_take_succ (p4TaskSpace P S6 mem₀) hi
    rw [ht] at hspsum
    have hsple := sum_take_le (p4TaskSpace P S6 mem₀) tasks (i + 1)
    have hfold : ∀ o : P4TaskOut, (qs ++ [(t, o)]).foldl (p4WVStep P S6 mem₀ OS) (S, v) =
        p4WVStep P S6 mem₀ OS (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v)) (t, o) := by
      intro o; rw [List.foldl_append]; rfl
    have hqs' : ∀ o : P4TaskOut, (qs ++ [(t, o)]).map Prod.fst = tasks.take (i + 1) := by
      intro o; rw [List.map_append, hqs, htake]; rfl
    -- Facts for the task at the current heap pointer.
    have hfooti' : ∀ a, bucketFoot spanTbl xi a → a < st.regs 3 := fun a ha => by
      rcases hfooti a ha with h | ⟨-, h⟩
      · have := hfoot a h; omega
      · exact h
    have hembfi' : ∀ a, embFoot eCap embH yi a → a < st.regs 3 := fun a ha => by
      rcases hembfi a ha with h | ⟨-, h⟩
      · have := hEmbF a h; omega
      · exact h
    have hSpanWsi : ∀ a, bucketFoot spanTbl xi a → a < ws ∨ ws + p4WsSize eCap ≤ a :=
      fun a ha => by
        rcases hfooti a ha with h | ⟨h, -⟩
        · exact hSpanWs a h
        · right; omega
    have hEmbWsi : ∀ a, embFoot eCap embH yi a → a < ws ∨ ws + p4WsSize eCap ≤ a :=
      fun a ha => by
        rcases hembfi a ha with h | ⟨h, -⟩
        · exact hEmbWs a h
        · right; omega
    have hOSi : ∀ e < eCap, st.mem (oldS + e) = if e ∈ OS then 1 else 0 := fun e he =>
      (hfr _ (hoFree e he).1 (hoFree e he).2).trans (hOS e he)
    have hoFooti : ∀ e < eCap, oldS + e < st.regs 3 ∧ ¬ bucketFoot spanTbl xi (oldS + e) :=
      fun e he => by
        refine ⟨by have := (hoFree e he).1; omega, fun hf => ?_⟩
        rcases hfooti _ hf with h | ⟨h, -⟩
        · exact (hoFree e he).2.1 h
        · have := (hoFree e he).1; omega
    have hspace_t : mem₀ t.batchPtr ≠ 0 → p4TaskSpace P S6 mem₀ t =
        dsUpdateOpSpace P d [0, t.batchPtr, t.W, 0] mem₀ +
          ((⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩ : DSHist).state P).G.E.sum
            (fun e => Read.walkWords (slotWalk P (S6.set ⟨t.slot, hs⟩
              (some ⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩)) t.slot e)) :=
      fun hb₀ => p4OnTask_of hs hdS6 hb₀
    have hspacei : st.mem t.batchPtr ≠ 0 →
        st.regs 3 + dsUpdateOpSpace P d [0, t.batchPtr, t.W, st.regs 3] st.mem +
          ((⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩ : DSHist).state P).G.E.sum
            (fun e => Read.walkWords (slotWalk P ((p4SpanAfter P S6 mem₀ (tasks.take i)).set
              ⟨t.slot, hs⟩ (some ⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩))
              t.slot e)) < 2 ^ P.w := by
      intro hb
      have hb₀ : mem₀ t.batchPtr ≠ 0 := fun h => hb (hb_eq.trans h)
      have hsum : ((⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩ :
          DSHist).state P).G.E.sum
            (fun e => Read.walkWords (slotWalk P ((p4SpanAfter P S6 mem₀ (tasks.take i)).set
              ⟨t.slot, hs⟩ (some ⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩))
              t.slot e)) =
          ((⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩ :
            DSHist).state P).G.E.sum
            (fun e => Read.walkWords (slotWalk P (S6.set ⟨t.slot, hs⟩
              (some ⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩)) t.slot e)) :=
        Finset.sum_congr rfl fun e _ => by
          rw [slotWalk_set_self P (p4SpanAfter P S6 mem₀ (tasks.take i)) S6 hs]
      rw [hsp_eq, hsum]
      have := hspace_t hb₀
      omega
    -- The run of the task.
    obtain ⟨o₁, st₁, c₁, hrun₁, hE, hN⟩ := asmFirstP4Task_runs hpS hfAfter hfUH hfD hfR hfDl
      hfC hfEdge hfPush hfMark hcopy hread (spanTbl := spanTbl) (s := t.slot)
      (batchPtr := t.batchPtr) (W := t.W) (hp := st.regs 3) (ws := ws) (eCap := eCap)
      (oldS := oldS) (embH := embH) (pos := st.pos) hs hcur (OS := OS)
      (S := (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v)).1)
      (v := (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v)).2) (y := yi) (ω := ω') hopB hw16 hWi
      hrepi hEmbi hOSi hoFooti (fun _ => hpre₁)
      (fun hb => (hcaps t htmem hs d hdS6 (fun h => hb (hb_eq.trans h))).1)
      (fun hb => (hcaps t htmem hs d hdS6 (fun h => hb (hb_eq.trans h))).2.1)
      (fun hb => (hcaps t htmem hs d hdS6 (fun h => hb (hb_eq.trans h))).2.2.1)
      heCap
      (fun hb => (hcaps t htmem hs d hdS6 (fun h => hb (hb_eq.trans h))).2.2.2)
      (by omega) hfooti' hembfi' hSpanWsi hEmbWsi hdisji ho_disj ho_w hzhp hspacei
    -- Reading the descriptor and calling the task.
    have hhp₀_lt : hp₀ < 2 ^ P.w := by omega
    have he3i : (Expr.bin .mul (.const 3) (.reg 8)).eval P.w st = some (3 * i) :=
      Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr8) (by omega)
    have heBase : (Expr.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 8))).eval P.w st =
        some (descPtr + 3 * i) :=
      Expr.eval_add (Expr.eval_reg_of_eq hr1) he3i (by omega)
    have heSlot : (Expr.load (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 8)))).eval P.w st =
        some t.slot :=
      Expr.eval_load_of_eq heBase hmem_slot
    set rA := Function.update st.regs 9 t.slot with hrA
    have heBaseA : (Expr.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 8))).eval P.w
        ⟨st.mem, rA, st.pos⟩ = some (descPtr + 3 * i) :=
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, hr1]))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [rA, hr8]))
          (by omega)) (by omega)
    have heBp : (Expr.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 8)))
        (.const 1))).eval P.w ⟨st.mem, rA, st.pos⟩ = some t.batchPtr :=
      Expr.eval_load_of_eq (Expr.eval_add heBaseA (Expr.eval_const (by omega)) (by omega)) hmem_bp
    set rB := Function.update rA 10 t.batchPtr with hrB
    have heBaseB : (Expr.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 8))).eval P.w
        ⟨st.mem, rB, st.pos⟩ = some (descPtr + 3 * i) :=
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [rB, rA, hr1]))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [rB, rA, hr8]))
          (by omega)) (by omega)
    have heW : (Expr.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 8)))
        (.const 2))).eval P.w ⟨st.mem, rB, st.pos⟩ = some t.W :=
      Expr.eval_load_of_eq (Expr.eval_add heBaseB (Expr.eval_const (by omega)) (by omega)) hmem_W
    set rC := Function.update rB 11 t.W with hrC
    have heArgs : evalArgs P.w ⟨st.mem, rC, st.pos⟩
        [.reg 0, .reg 9, .reg 10, .reg 11, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7] =
        some [spanTbl, t.slot, t.batchPtr, t.W, st.regs 3, ws, eCap, oldS, embH] :=
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC, rB, rA, hr0])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC, rB, rA])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC, rB])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC, rB, rA])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC, rB, rA, hr4])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC, rB, rA, hr5])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC, rB, rA, hr6])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC, rB, rA, hr7])) <| evalArgs_nil _ _
    have hr_call : Runs P.w p ω'
        (.call 3 fTask [.reg 0, .reg 9, .reg 10, .reg 11, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7])
        ⟨st.mem, rC, st.pos⟩ .normal ⟨st₁.mem, Function.update rC 3 o₁.value, st₁.pos⟩
        (argsSize [.reg 0, .reg 9, .reg 10, .reg 11, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7] +
          c₁ + 1) :=
      runs_call_iff.mpr ⟨_, _, o₁, st₁, c₁, heArgs, hfTask, hrun₁, rfl, rfl, rfl⟩
    have hr_a11 : Runs P.w p ω'
        (.assign 11 (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 8)))
          (.const 2))))
        ⟨st.mem, rB, st.pos⟩ .normal ⟨st.mem, rC, st.pos⟩
        ((Expr.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 8)))
          (.const 2))).size + 1) :=
      runs_assign_iff.mpr ⟨t.W, heW, rfl, rfl, rfl⟩
    have hr_a10 : Runs P.w p ω'
        (.assign 10 (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 8)))
          (.const 1))))
        ⟨st.mem, rA, st.pos⟩ .normal ⟨st.mem, rB, st.pos⟩
        ((Expr.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 8)))
          (.const 1))).size + 1) :=
      runs_assign_iff.mpr ⟨t.batchPtr, heBp, rfl, rfl, rfl⟩
    have hr_a9 : Runs P.w p ω'
        (.assign 9 (.load (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 8)))))
        st .normal ⟨st.mem, rA, st.pos⟩
        ((Expr.load (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 8)))).size + 1) :=
      runs_assign_iff.mpr ⟨t.slot, heSlot, rfl, rfl, rfl⟩
    have hr_all := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_a9,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_a10,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_a11, hr_call, rfl⟩), rfl⟩), rfl⟩)
    have hR0 : (Function.update (Function.update rC 3 o₁.value) 8 (i + 1)) 0 = spanTbl := by
      simp [rC, rB, rA, hr0]
    have hR1 : (Function.update (Function.update rC 3 o₁.value) 8 (i + 1)) 1 = descPtr := by
      simp [rC, rB, rA, hr1]
    have hR2 : (Function.update (Function.update rC 3 o₁.value) 8 (i + 1)) 2 = tasks.length := by
      simp [rC, rB, rA, hr2]
    have hR3 : (Function.update (Function.update rC 3 o₁.value) 8 (i + 1)) 3 = o₁.value := by
      simp
    have hR4 : (Function.update (Function.update rC 3 o₁.value) 8 (i + 1)) 4 = ws := by
      simp [rC, rB, rA, hr4]
    have hR5 : (Function.update (Function.update rC 3 o₁.value) 8 (i + 1)) 5 = eCap := by
      simp [rC, rB, rA, hr5]
    have hR6 : (Function.update (Function.update rC 3 o₁.value) 8 (i + 1)) 6 = oldS := by
      simp [rC, rB, rA, hr6]
    have hR7 : (Function.update (Function.update rC 3 o₁.value) 8 (i + 1)) 7 = embH := by
      simp [rC, rB, rA, hr7]
    have hR8 : (Function.update (Function.update rC 3 o₁.value) 8 (i + 1)) 8 = i + 1 := by
      simp
    have hRi : (Function.update rC 3 o₁.value) 8 = i := by simp [rC, rB, rA, hr8]
    have hcall_cost : argsSize [.reg 0, .reg 9, .reg 10, .reg 11, .reg 3, .reg 4, .reg 5,
        .reg 6, .reg 7] = 9 := by simp [argsSize, Expr.size]
    by_cases hb : st.mem t.batchPtr = 0
    · -- An empty batch: nothing changes.
      have hb₀ : mem₀ t.batchPtr = 0 := hb_eq ▸ hb
      obtain ⟨ho₁, hm₁, hc₁⟩ := hE hb
      have hS_eq : p4SpanAfter P S6 mem₀ (tasks.take (i + 1)) =
          p4SpanAfter P S6 mem₀ (tasks.take i) := by
        rw [hSpan_succ]; exact p4OnTask_empty hs hdS6 hb₀
      have hWV : p4WVStep P S6 mem₀ OS (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v))
          (t, ⟨[], [], []⟩) = qs.foldl (p4WVStep P S6 mem₀ OS) (S, v) :=
        p4OnTask_empty (t := t) hs hdS6 hb₀
      have hpay0 : p4TaskPay P S6 mem₀ t = 0 := p4OnTask_empty hs hdS6 hb₀
      refine ⟨.normal, _, _, hr_all, ⟨?_, hRi⟩, ?_⟩
      · show P4LoopInvAt P S6 x6 spanTbl descPtr hp₀ ws eCap oldS embH OS S v y tasks mem₀ (i + 1)
          (Function.update (Function.update rC 3 o₁.value) 8 (i + 1)) st₁.mem
        rw [P4LoopInvAt, hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, ho₁, hm₁]
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hhp_lo, by simp only [Outcome.value]; omega,
          hzhp, hfr, fun j hj => ?_, qs ++ [(t, ⟨[], [], []⟩)], xi, yi, hqs' _, fun q hq => ?_,
          ?_, ?_, ?_, hfooti, hembfi, hdisji⟩
        · rcases Nat.lt_or_ge j i with hji | hji
          · exact hph j hji
          · have hj' : j = i := by omega
            subst hj'
            rw [hS_eq, hgetD, hpay0]; omega
        · rcases List.mem_append.mp hq with hq | hq
          · exact hqsOK q hq
          · simp only [List.mem_singleton] at hq
            subst hq
            intro _ _ _ hb'
            exact absurd hb₀ hb'
        · rw [hfold, hWV]; exact hWi
        · rw [hfold, hWV]; exact hEmbi
        · rw [hS_eq]; exact hrepi
      · simp only [p4LoopStepCost, Expr.size, hcall_cost]
        omega
    · -- A batch that is not empty: the task updates its slot.
      have hb₀ : mem₀ t.batchPtr ≠ 0 := fun h => hb (hb_eq.trans h)
      obtain ⟨h₁, mem₁, x', UH, dL, rL, hh₁lo, hh₁hi, hfr₁, hft₁, hPerm, hAppl, hdNd, hdFs,
        hrNd, hrFs, hT82, hAfter, hcost₁⟩ := hN hb
      rw [hopB] at hPerm hAppl hdFs hrFs hT82 hAfter hcost₁
      rw [hsp_eq] at hh₁hi
      rw [hac_eq] at hcost₁
      obtain ⟨ho₁, hWs₁, ⟨y₁, hEmb₁, hEmbFt₁⟩, hrep₁, hz₁, hfr₂⟩ := hAfter
      have hnd_eL := p4TaskScan_copyBuf_nodup P
        ⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩ OS UH dL rL
        (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v)).1
      have hwords := slotListWalkWords_le_sum P (S6.set ⟨t.slot, hs⟩
        (some ⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩)) t.slot hnd_eL
        (fun e he => mem_p4TaskScan_copyBuf he)
      rw [← slotListWalkWords_set_self P (p4SpanAfter P S6 mem₀ (tasks.take i)) S6 hs]
        at hwords
      have hsp_t := hspace_t hb₀
      have hpay_t : p4TaskPay P S6 mem₀ t = dsUpdateAmortCost P d [0, t.batchPtr, t.W, 0] mem₀ +
          p4TaskWorkOf P S6 t.slot hs d (decodeBatch mem₀ t.batchPtr (d.state P).G).1 + 600 :=
        p4OnTask_of hs hdS6 hb₀
      have hwork : 340 * UH.length + 170 * dL.length + 135 * rL.length +
          ((p4TaskScan P ⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩ OS UH
            dL rL (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v)).1).copyBuf.map (p4DleftEdgeCost P
              ⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩)).sum +
          142 * slotListCopyWork P ((p4SpanAfter P S6 mem₀ (tasks.take i)).set ⟨t.slot, hs⟩
              (some ⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩)) t.slot
            ⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩
            (p4TaskScan P ⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩ OS UH
              dL rL (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v)).1).copyBuf ≤
          p4TaskWorkOf P S6 t.slot hs d (decodeBatch mem₀ t.batchPtr (d.state P).G).1 := by
        have h1 := hPerm.length_eq
        have h2 : dL.length = (update (d.state P) (decodeBatch mem₀ t.batchPtr (d.state P).G).1
            (canonicalSparsify P.impl)).D.card := by
          rw [← hdFs, List.toFinset_card_of_nodup hdNd]
        have h3 : rL.length = (updateReembSet (d.state P)
            (decodeBatch mem₀ t.batchPtr (d.state P).G).1 (canonicalSparsify P.impl)).card := by
          rw [← hrFs, List.toFinset_card_of_nodup hrNd]
        have h4 := p4_copy_work_le P (S6.set ⟨t.slot, hs⟩
          (some ⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩)) t.slot
          ⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩ hnd_eL
          (X := p4CopyCand P d (decodeBatch mem₀ t.batchPtr (d.state P).G).1) (fun e he => by
            obtain ⟨h1, h2, h3⟩ := mem_p4TaskScan_copyBuf_cand he
            unfold p4CopyCand
            simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]
            refine ⟨⟨?_, h2⟩, h3⟩
            rcases h1 with h1 | h1
            · left; rwa [← uhDelFinset_perm hPerm]
            · right; rw [← hrFs]; exact List.mem_toFinset.mpr h1)
        rw [slotListCopyWork_set_self P (p4SpanAfter P S6 mem₀ (tasks.take i)) S6 hs]
        unfold p4TaskWorkOf
        omega
      have hval : o₁.value = h₁ + slotListWalkWords P
          ((p4SpanAfter P S6 mem₀ (tasks.take i)).set ⟨t.slot, hs⟩
            (some ⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩)) t.slot
          (p4TaskScan P ⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩ OS UH
            dL rL (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v)).1).copyBuf := by
        rw [ho₁]; rfl
      rw [← hval] at hz₁ hEmbFt₁
      have hS_succ : p4SpanAfter P S6 mem₀ (tasks.take (i + 1)) =
          (p4SpanAfter P S6 mem₀ (tasks.take i)).set ⟨t.slot, hs⟩
            (some ⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩) := by
        rw [hSpan_succ]; exact p4OnTask_of hs hdS6 hb₀
      have hWV : p4WVStep P S6 mem₀ OS (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v))
          (t, ⟨UH, dL, rL⟩) =
          (p4TaskWS P ⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩ OS UH dL
            rL (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v)).1,
           (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v)).2.apply (slotChange P (S6.set ⟨t.slot, hs⟩
            (some ⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩)) t.slot
            (p4TaskScan P ⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩ OS
              UH dL rL (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v)).1).copyBuf)) :=
        p4OnTask_of (t := t) hs hdS6 hb₀
      rw [slotChange_set_self P (p4SpanAfter P S6 mem₀ (tasks.take i)) S6 hs] at hEmb₁
      have hlo₁ : st.regs 3 ≤ o₁.value := by omega
      refine ⟨.normal, _, _, hr_all, ⟨?_, hRi⟩, ?_⟩
      · show P4LoopInvAt P S6 x6 spanTbl descPtr hp₀ ws eCap oldS embH OS S v y tasks mem₀ (i + 1)
          (Function.update (Function.update rC 3 o₁.value) 8 (i + 1)) st₁.mem
        rw [P4LoopInvAt, hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8]
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by omega, by omega, hz₁, fun a ha hfa => ?_,
          fun j hj => ?_, qs ++ [(t, ⟨UH, dL, rL⟩)], x', y₁, hqs' _, fun q hq => ?_, ?_, ?_, ?_,
          fun a ha => ?_, fun a ha => ?_, fun a ha hb' => ?_⟩
        · -- The frame.
          have hne : ¬ embFoot eCap embH yi a := fun he => by
            rcases hembfi a he with h | ⟨h, -⟩
            · exact hfa.2.1 h
            · omega
          have hnb : ¬ bucketFoot spanTbl xi a := fun hf => by
            rcases hfooti a hf with h | ⟨h, -⟩
            · exact hfa.1 h
            · omega
          rw [hfr₂ a (by omega) hne hfa.2.2, hfr₁ a (by omega) hnb, hfr a ha hfa]
        · rcases Nat.lt_or_ge j i with hji | hji
          · exact hph j hji
          · have hj' : j = i := by omega
            subst hj'
            rw [hS_succ, hgetD, hpay_t]; omega
        · rcases List.mem_append.mp hq with hq | hq
          · exact hqsOK q hq
          · simp only [List.mem_singleton] at hq
            subst hq
            intro hs' d₂ hd₂ _
            have hdd : d₂ = d := Option.some.inj (hd₂.symm.trans hdS6)
            subst hdd
            exact ⟨hPerm, hAppl, hdNd, hdFs, hrNd, hrFs, hT82⟩
        · rw [hfold, hWV]; exact hWs₁
        · rw [hfold, hWV]; exact hEmb₁
        · rw [hS_succ]; exact hrep₁
        · rcases hft₁ a ha with h | ⟨h, h'⟩
          · rcases hfooti a h with h | ⟨h, h'⟩
            · exact Or.inl h
            · exact Or.inr ⟨h, by omega⟩
          · exact Or.inr ⟨by omega, by omega⟩
        · rcases hEmbFt₁ a ha with h | ⟨h, h'⟩
          · rcases hembfi a h with h | ⟨h, h'⟩
            · exact Or.inl h
            · exact Or.inr ⟨h, by omega⟩
          · exact Or.inr ⟨by omega, h'⟩
        · rcases hEmbFt₁ a ha with he | ⟨he, -⟩
          · rcases hft₁ a hb' with hf | ⟨hf, -⟩
            · exact hdisji a he hf
            · have := hembfi' a he; omega
          · rcases hft₁ a hb' with hf | ⟨-, hf⟩
            · have := hfooti' a hf; omega
            · omega
      · simp only [p4LoopStepCost, Expr.size, hcall_cost]
        rw [hgetD, hS_succ, hpay_t]
        omega
  -- The whole procedure: the loop, then `ret (reg 3)`.
  have hloop := Triple.forRange_le
    (P := fun st : State => st.mem = mem₀ ∧ st.regs 0 = spanTbl ∧ st.regs 1 = descPtr ∧
      st.regs 2 = tasks.length ∧ st.regs 3 = hp₀ ∧ st.regs 4 = ws ∧ st.regs 5 = eCap ∧
      st.regs 6 = oldS ∧ st.regs 7 = embH)
    (Inv := P4LoopInv P S6 x6 spanTbl descPtr hp₀ ws eCap oldS embH OS S v y tasks mem₀)
    (p4LoopStepCost P S6 mem₀ tasks) 0 tasks.length (Nat.zero_le _) hw1 (fun _ => hn_lt)
    (fun st hst => by
      obtain ⟨hmem, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7⟩ := hst
      refine ⟨Expr.eval_const (by omega), ?_⟩
      show P4LoopInvAt P S6 x6 spanTbl descPtr hp₀ ws eCap oldS embH OS S v y tasks mem₀ 0
        (Function.update st.regs 8 0) st.mem
      have hR3 : Function.update st.regs 8 0 3 = hp₀ := by simp [hr3]
      rw [hmem, P4LoopInvAt, hR3]
      refine ⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr4], by simp [hr5],
        by simp [hr6], by simp [hr7], by simp, le_rfl, by simp, hz,
        fun a _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _), [], x6, y, rfl,
        fun q hq => absurd hq List.not_mem_nil, hW, hEmb, hS6, fun a ha => Or.inl ha,
        fun a ha => Or.inl ha, hDisj⟩)
    (fun i st _ _ hInv => hInv.2.2.2.2.2.2.2.1)
    (fun i st _ _ hInv => Expr.eval_reg_of_eq hInv.2.2.1)
    (fun i _ hi => hbody i hi)
  obtain ⟨oL, stL, cL, hrunL, hpostL, hcL⟩ := hloop
    (startState [spanTbl, descPtr, tasks.length, hp₀, ws, eCap, oldS, embH] mem₀ pos) ω
    ⟨rfl, by simp [startState], by simp [startState], by simp [startState], by simp [startState],
      by simp [startState], by simp [startState], by simp [startState], by simp [startState]⟩
  cases oL with
  | returned _ => cases hpostL
  | normal =>
  obtain ⟨-, -, -, -, -, -, -, -, hloE, hhiE, hzE, hfrE, hphE, qs, x', y', hqs, hqsOK, hWE,
    hEmbE, hrepE, hfootE, hembfE, hdisjE⟩ := hpostL
  rw [List.take_length] at hhiE hqs hrepE
  have hr_ret : Runs P.w p ω (.ret (.reg 3)) stL (.returned (stL.regs 3)) stL
      ((Expr.reg 3).size + 1) :=
    runs_ret_iff.mpr ⟨stL.regs 3, Expr.eval_reg_of_eq rfl, rfl, rfl, rfl⟩
  have hr_full : Runs P.w p ω (asmFirstP4LoopStmt fTask)
      (startState [spanTbl, descPtr, tasks.length, hp₀, ws, eCap, oldS, embH] mem₀ pos)
      (.returned (stL.regs 3)) stL (cL + ((Expr.reg 3).size + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨stL, _, _, hrunL, hr_ret, rfl⟩)
  -- The cost: sum the rounds and telescope the potential (`sum_tele`).
  have hrc : rangeCost (p4LoopStepCost P S6 mem₀ tasks) 0 tasks.length =
      ((List.range tasks.length).map (p4LoopStepCost P S6 mem₀ tasks)).sum :=
    rangeCost_zero_eq_range _ _
  have htele := sum_tele (fun j => p4TaskPay P S6 mem₀ (tasks.getD j ⟨0, 0, 0⟩))
    (fun j => specPhi P (p4SpanAfter P S6 mem₀ (tasks.take j))) tasks.length hphE
  have hstep_sum : ((List.range tasks.length).map (p4LoopStepCost P S6 mem₀ tasks)).sum =
      60 * tasks.length + ((List.range tasks.length).map fun j =>
        p4TaskPay P S6 mem₀ (tasks.getD j ⟨0, 0, 0⟩) +
          specPhi P (p4SpanAfter P S6 mem₀ (tasks.take j)) -
          specPhi P (p4SpanAfter P S6 mem₀ (tasks.take (j + 1)))).sum := by
    have h1 : ∀ (n : ℕ) (f : ℕ → ℕ),
        ((List.range n).map fun j => 60 + f j).sum = 60 * n + ((List.range n).map f).sum := by
      intro n f; induction n with
      | zero => simp
      | succ m ih => simp [List.range_succ, List.sum_append, ih]; omega
    exact h1 _ _
  have hmap_sum : ((List.range tasks.length).map fun j =>
        p4TaskPay P S6 mem₀ (tasks.getD j ⟨0, 0, 0⟩)).sum =
      (tasks.map (p4TaskPay P S6 mem₀)).sum := by
    congr 1
    apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp only [List.length_map, List.length_range] at h₁
    simp [List.getElem?_eq_getElem h₁]
  have hplus_sum : (tasks.map fun t => p4TaskPay P S6 mem₀ t + 70).sum =
      (tasks.map (p4TaskPay P S6 mem₀)).sum + 70 * tasks.length := by
    have haux : ∀ (l : List SpanUpdTask), (l.map fun t => p4TaskPay P S6 mem₀ t + 70).sum =
        (l.map (p4TaskPay P S6 mem₀)).sum + 70 * l.length := by
      intro l; induction l with
      | nil => simp
      | cons a as ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega
    exact haux tasks
  have hphi0 : specPhi P (p4SpanAfter P S6 mem₀ (tasks.take 0)) = specPhi P S6 := rfl
  have hphiN : specPhi P (p4SpanAfter P S6 mem₀ (tasks.take tasks.length)) =
      specPhi P (p4SpanAfter P S6 mem₀ tasks) := by rw [List.take_length]
  refine ⟨.returned (stL.regs 3), stL, _, hr_full, qs, x', y', hqs, hqsOK, hWE, hEmbE, hrepE,
    hloE, hhiE, hzE, hfrE, hfootE, hembfE, hdisjE, ?_⟩
  simp only [Expr.size] at hcL ⊢
  rw [hrc, hstep_sum] at hcL
  rw [hplus_sum]
  rw [hmap_sum, hphi0, hphiN] at htele
  omega

end

end MinCostFlow.SparseCore.Program
