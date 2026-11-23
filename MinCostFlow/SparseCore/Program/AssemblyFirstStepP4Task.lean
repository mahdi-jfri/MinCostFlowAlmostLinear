module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4After
public import MinCostFlow.SparseCore.Program.AssemblyFirstSpan

import WordRAM.Tactic

/-!
# One task of Phase 4: the update of one slot and the work after it (`AssemblyFirstStepP4Task`)

A task of Phase 4 belongs to one old active slot whose bundle changed. It gives the batch of the
slot to the slot's spanner (operation `1` of the spanners, `bucketSpannerDS`), and then runs
`asmFirstP4AfterStmt` on the outputs of the update at once, before a later spanner call can write
over them. When the batch is empty, the task does nothing: the slot keeps its history.

* `asmFirstP4TaskStmt fUpd fAfter`, with arguments
  `[spanTbl, slot, batchPtr, W, hp, ws, eCap, oldS, embH]`.
* `P4TaskPost`: what a task leaves, in both cases.
* `asmFirstP4Task_runs`: the run lemma.

Two pure facts are proved first: the copy buffer of `p4TaskScan` has no repeated edge
(`p4TaskScan_copyBuf_nodup`), so the words of its walks are at most the words of the walks of all
edges of the slot's graph (`slotListWalkWords_le_sum`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Read MinCostFlow.SparseCore.Program.Restart

/-! ## The copy buffer has no repeated edge -/

public section

/-- The copy buffer has no repeated edge, and each of its edges has been seen. -/
@[expose] def CopyBufOK (T : Phase4WS) : Prop := T.copyBuf.Nodup ∧ ∀ x ∈ T.copyBuf, x ∈ T.seenCopy

theorem copyBufOK_pushCopy {T : Phase4WS} (h : CopyBufOK T) (e : ℕ) :
    CopyBufOK (pushCopy T e) := by
  unfold pushCopy
  split_ifs with he
  · exact h
  · refine ⟨List.nodup_append.mpr ⟨h.1, List.nodup_singleton e, ?_⟩, fun x hx => ?_⟩
    · intro a ha b hb hab
      simp only [List.mem_singleton] at hb
      subst hb hab
      exact he (h.2 a ha)
    · rcases List.mem_append.mp hx with hx | hx
      · exact Finset.mem_insert_of_mem (h.2 x hx)
      · simp only [List.mem_singleton] at hx
        subst hx
        exact Finset.mem_insert_self _ _

theorem copyBufOK_of_eq {T T' : Phase4WS} (h : CopyBufOK T) (hc : T'.copyBuf = T.copyBuf)
    (hs : T'.seenCopy = T.seenCopy) : CopyBufOK T' := by
  unfold CopyBufOK; rw [hc, hs]; exact h

theorem p4StepEdge_seenCopy (GE HE : Finset ℕ) (fD fDel fIns : Bool) (S : Phase4WS) (e : ℕ) :
    (p4StepEdge GE HE fD fDel fIns false S e).seenCopy = S.seenCopy := by
  cases fD <;> cases fDel <;> cases fIns <;> simp [p4StepEdge, p4Mark]

theorem copyBufOK_p4StepEdge {GE HE : Finset ℕ} {fD fDel fIns fCopy : Bool} {S : Phase4WS}
    (h : CopyBufOK S) (e : ℕ) : CopyBufOK (p4StepEdge GE HE fD fDel fIns fCopy S e) := by
  have h0 : CopyBufOK (p4StepEdge GE HE fD fDel fIns false S e) :=
    copyBufOK_of_eq h (p4StepEdge_copyBuf _ _ _ _ _ _ _) (p4StepEdge_seenCopy _ _ _ _ _ _ _)
  cases fCopy with
  | false => exact h0
  | true =>
    have hp : p4StepEdge GE HE fD fDel fIns true S e =
        pushCopy (p4StepEdge GE HE fD fDel fIns false S e) e := by
      simp only [p4StepEdge, Bool.false_eq_true, ↓reduceIte]
    rw [hp]; exact copyBufOK_pushCopy h0 e

/-- The copy buffer after the scans of `U_H`, `D` and `R` has no repeated edge, since it starts
empty and every push into it checks the seen flags (`pushCopy`). -/
theorem p4TaskScan_copyBuf_nodup (P : DSParams) (d : DSHist) (OS : Finset ℕ) (UH : List Update)
    (D R : List ℕ) (S : Phase4WS) : (p4TaskScan P d OS UH D R S).copyBuf.Nodup := by
  classical
  have hUH : ∀ T u, CopyBufOK T →
      CopyBufOK (p4StepUH (d.state P).G.E (d.state P).H.E OS true T u) := by
    intro T u hT
    cases u with
    | insert e a b => exact copyBufOK_p4StepEdge hT e
    | delete e => exact copyBufOK_p4StepEdge hT e
    | split a b c f => exact hT
  have hD : ∀ T e, CopyBufOK T → CopyBufOK (p4StepD (d.state P).G.E (d.state P).H.E T e) :=
    fun T e hT => copyBufOK_of_eq hT rfl rfl
  have hR : ∀ T e, CopyBufOK T →
      CopyBufOK (p4StepR (d.state P).G.E (d.state P).H.E true T e) := by
    intro T e hT
    have h1 : CopyBufOK { T with reemb := pushDedup T.reemb e } := copyBufOK_of_eq hT rfl rfl
    unfold p4StepR
    split_ifs
    · exact copyBufOK_pushCopy h1 e
    · exact h1
  exact (foldl_keeps CopyBufOK _ hR R _ (foldl_keeps CopyBufOK _ hD D _
    (foldl_keeps CopyBufOK _ hUH UH _ ⟨List.nodup_nil, fun _ h => (by cases h)⟩))).1

/-- The words of the walks of a list of distinct edges of a set `E` are at most the words of the
walks of all edges of `E`. -/
theorem slotListWalkWords_le_sum (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap) (s : ℕ)
    {eL : List ℕ} {E : Finset ℕ} (hnd : eL.Nodup) (hsub : ∀ e ∈ eL, e ∈ E) :
    slotListWalkWords P S6 s eL ≤ E.sum fun e => Read.walkWords (slotWalk P S6 s e) := by
  classical
  unfold slotListWalkWords
  rw [← List.sum_toFinset _ hnd]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun e he => hsub e (List.mem_toFinset.mp he))
    (fun _ _ _ => Nat.zero_le _)

/-- A batch read from memory has as many updates as its first word says. -/
theorem decodeBatchBody_length (mem : ℕ → ℕ) :
    ∀ (n a : ℕ) (G : MGraph), (decodeBatchBody mem n a G).1.length = n
  | 0, _, _ => rfl
  | n + 1, a, G => by
    simp only [decodeBatchBody, List.length_cons]
    rw [decodeBatchBody_length mem n]

end

/-! ## The procedure and what it leaves -/

@[expose] public section

/-- **One task of Phase 4**, `[spanTbl, slot, batchPtr, W, hp, ws, eCap, oldS, embH]`. When the
batch at `batchPtr` is not empty, it updates the slot's spanner with it (`fUpd`, operation `1`
of the spanners, heap pointer `hp`), and then runs the work after the update (`fAfter`), whose
outputs start at `hp + W`. It returns the new heap pointer. When the batch is empty, it returns
`hp` and does nothing. -/
def asmFirstP4TaskStmt (fUpd fAfter : ℕ) : Stmt :=
  .cond (.load (.reg 2))
    (.call 9 fUpd [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4] ;;
     .call 10 fAfter [.reg 0, .reg 1, .bin .add (.reg 4) (.reg 3), .reg 5, .reg 6, .reg 7,
       .reg 8, .reg 9] ;;
     .ret (.reg 10))
    (.ret (.reg 4))

/-- What one task leaves, from the memory `mem₀` and the spanners `S6` (meta `x6`), where slot `s`
holds the history `d`. With an empty batch, the task returns `hp`, keeps the memory, and costs at
most `10`. Otherwise let `U` be the batch, `d'` the history with `U` appended and `S'` the
spanners with `d'` at slot `s`. There are a heap pointer `h₁` and a memory `mem₁` right after the
update (the update keeps every cell below `hp` outside the old footprint of the spanners), a meta
`x'` of the spanners whose footprint grows only in `[hp, h₁)`, and the outputs `UH`, `dL`, `rL`
of the update with the facts of `DSUpdatePost`, such that the work after the update ends in
`P4AfterPost` from `mem₁`. The cost and the potential of the spanners are paid by the amortized
cost of the update and the cost of the work after it. -/
def P4TaskPost (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (x6 : BucketSpannerMeta P.L cap) (spanTbl s batchPtr W hp ws eCap embH : ℕ) (hs : s < cap)
    (d : DSHist) (OS : Finset ℕ) (S : Phase4WS) (v : EmbView) (y : EmbConc) (mem₀ : ℕ → ℕ)
    (o : Outcome) (st' : State) (c : ℕ) : Prop :=
  (mem₀ batchPtr = 0 → o = .returned hp ∧ st'.mem = mem₀ ∧ c ≤ 10) ∧
  (mem₀ batchPtr ≠ 0 →
    ∃ (h₁ : ℕ) (mem₁ : ℕ → ℕ) (x' : BucketSpannerMeta P.L cap) (UH : List Update)
      (dL rL : List ℕ),
      hp ≤ h₁ ∧ h₁ ≤ hp + dsUpdateOpSpace P d [0, batchPtr, W, hp] mem₀ ∧
      (∀ a < hp, ¬ bucketFoot spanTbl x6 a → mem₁ a = mem₀ a) ∧
      (∀ a, bucketFoot spanTbl x' a → bucketFoot spanTbl x6 a ∨ (hp ≤ a ∧ a < h₁)) ∧
      UH.Perm (update (d.state P) (opBatch P d [0, batchPtr, W, hp] mem₀).1
        (canonicalSparsify P.impl)).UH ∧
      (d.state P).H.applyBatch UH = (update (d.state P) (opBatch P d [0, batchPtr, W, hp] mem₀).1
        (canonicalSparsify P.impl)).state.H ∧
      dL.Nodup ∧ dL.toFinset = (update (d.state P) (opBatch P d [0, batchPtr, W, hp] mem₀).1
        (canonicalSparsify P.impl)).D ∧
      rL.Nodup ∧ rL.toFinset = updateReembSet (d.state P) (opBatch P d [0, batchPtr, W, hp] mem₀).1
        (canonicalSparsify P.impl) ∧
      Theorem82Clauses d.G₀ P.L P.splitBound (dsSparsifyParams P) (canonicalSparsify P.impl)
        (d.Us ++ [(opBatch P d [0, batchPtr, W, hp] mem₀).1]) ∧
      P4AfterPost P (S6.set ⟨s, hs⟩ (some ⟨d.G₀, d.Us ++ [(opBatch P d [0, batchPtr, W, hp] mem₀).1]⟩))
        x' spanTbl s ws eCap embH h₁ ⟨d.G₀, d.Us ++ [(opBatch P d [0, batchPtr, W, hp] mem₀).1]⟩
        OS UH dL rL S v y mem₁ o st' ∧
      c + specPhi P (S6.set ⟨s, hs⟩
          (some ⟨d.G₀, d.Us ++ [(opBatch P d [0, batchPtr, W, hp] mem₀).1]⟩)) ≤
        dsUpdateAmortCost P d [0, batchPtr, W, hp] mem₀ + specPhi P S6 +
        340 * UH.length + 170 * dL.length + 135 * rL.length +
        ((p4TaskScan P ⟨d.G₀, d.Us ++ [(opBatch P d [0, batchPtr, W, hp] mem₀).1]⟩ OS UH dL rL
          S).copyBuf.map (p4DleftEdgeCost P
            ⟨d.G₀, d.Us ++ [(opBatch P d [0, batchPtr, W, hp] mem₀).1]⟩)).sum +
        142 * slotListCopyWork P (S6.set ⟨s, hs⟩
            (some ⟨d.G₀, d.Us ++ [(opBatch P d [0, batchPtr, W, hp] mem₀).1]⟩)) s
          ⟨d.G₀, d.Us ++ [(opBatch P d [0, batchPtr, W, hp] mem₀).1]⟩
          (p4TaskScan P ⟨d.G₀, d.Us ++ [(opBatch P d [0, batchPtr, W, hp] mem₀).1]⟩ OS UH dL rL
            S).copyBuf + 600)

end

public section

theorem asmFirstP4TaskStmt_noRand (fUpd fAfter : ℕ) : (asmFirstP4TaskStmt fUpd fAfter).NoRand := by
  simp [asmFirstP4TaskStmt, Stmt.NoRand]

end

/-- A call whose body is given by a run, at the start of a sequence. -/
private theorem runs_seq_callRuns_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ}
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

/-! ## The run of one task -/

public section

set_option maxHeartbeats 1600000 in
/-- **The run of one task.** The slot `s` of the spanners at `spanTbl` holds the history `d`, the
batch `U` at `batchPtr` (with `W` words) is read on its graph, and everything the task reads or
keeps lies below the heap pointer `hp`: the spanners, the embedding at `embH`, the workspace at
`ws` and the presence array of the old output graph at `oldS`. The workspace is apart from the
spanners and the embedding, which are apart from each other. When the batch is not empty, the
batch meets `DSUpdatePre`, the outputs of the update and the walks of the new spanner have their
edges below `eCap`, and there is room for the update and for the walks of all edges of the new
graph. Then `asmFirstP4TaskStmt` ends in `P4TaskPost`. -/
theorem asmFirstP4Task_runs {P : DSParams} {cap : ℕ} {bSpan fAfter : ℕ}
    {fScanUH fScanD fScanR fDleft fCopy fEdge fPush fMark bRead bCopy : ℕ} {p : Program}
    (hpS : p.HasAt bSpan (bucketSpannerProcs P.impl bSpan))
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
    {spanTbl s batchPtr W hp ws eCap oldS embH pos : ℕ} {S6 : BucketSpannerState cap}
    {x6 : BucketSpannerMeta P.L cap} (hs : s < cap) {d : DSHist} (hSj : S6 ⟨s, hs⟩ = some d)
    {OS : Finset ℕ} {S : Phase4WS} {v : EmbView} {y : EmbConc} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    {U : List Update} (hU : (opBatch P d [0, batchPtr, W, hp] mem₀).1 = U)
    (hw16 : 16 ≤ 2 ^ P.w)
    (hW : Phase4WSAt mem₀ ws eCap S)
    (hS6 : (bucketSpannerRep P cap).rep spanTbl S6 x6 mem₀)
    (hEmb : (embRep eCap).rep embH v y mem₀)
    (hOS : ∀ e < eCap, mem₀ (oldS + e) = if e ∈ OS then 1 else 0)
    (hoFoot : ∀ e < eCap, oldS + e < hp ∧ ¬ bucketFoot spanTbl x6 (oldS + e))
    (hpre : mem₀ batchPtr ≠ 0 → DSUpdatePre P d [0, batchPtr, W, hp] mem₀)
    (hUHcap : mem₀ batchPtr ≠ 0 → ∀ u ∈ (update (d.state P) U (canonicalSparsify P.impl)).UH, UpdEdgeBelow eCap u)
    (hDcap : mem₀ batchPtr ≠ 0 → ∀ e ∈ (update (d.state P) U (canonicalSparsify P.impl)).D, e < eCap)
    (hRcap : mem₀ batchPtr ≠ 0 → ∀ e ∈ updateReembSet (d.state P) U (canonicalSparsify P.impl), e < eCap)
    (heCap : eCap ≤ P.eCap)
    (hWalkCap : mem₀ batchPtr ≠ 0 → ∀ e ∈ ((⟨d.G₀, d.Us ++ [U]⟩ : DSHist).state P).G.E,
      ∀ q ∈ piTotal ((⟨d.G₀, d.Us ++ [U]⟩ : DSHist).state P) e, q.1 < eCap)
    (hWsH : ws + p4WsSize eCap ≤ hp)
    (hfoot : ∀ a, bucketFoot spanTbl x6 a → a < hp)
    (hEmbF : ∀ a, embFoot eCap embH y a → a < hp)
    (hSpanWs : ∀ a, bucketFoot spanTbl x6 a → a < ws ∨ ws + p4WsSize eCap ≤ a)
    (hEmbWs : ∀ a, embFoot eCap embH y a → a < ws ∨ ws + p4WsSize eCap ≤ a)
    (hDisj : ∀ a, embFoot eCap embH y a → ¬ bucketFoot spanTbl x6 a)
    (ho_disj : oldS + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ oldS) (ho_w : oldS + eCap < 2 ^ P.w)
    (hz : ZeroFrom mem₀ hp)
    (hspace : mem₀ batchPtr ≠ 0 → hp + dsUpdateOpSpace P d [0, batchPtr, W, hp] mem₀ +
      ((⟨d.G₀, d.Us ++ [U]⟩ : DSHist).state P).G.E.sum
        (fun e => Read.walkWords (slotWalk P (S6.set ⟨s, hs⟩ (some ⟨d.G₀, d.Us ++ [U]⟩)) s e)) <
      2 ^ P.w) :
    ∃ o st' c, Runs P.w p ω (asmFirstP4TaskStmt (bSpan + bsIdxOp0 + 1) fAfter)
        (startState [spanTbl, s, batchPtr, W, hp, ws, eCap, oldS, embH] mem₀ pos) o st' c ∧
      P4TaskPost P S6 x6 spanTbl s batchPtr W hp ws eCap embH hs d OS S v y mem₀ o st' c := by
  classical
  subst hU
  have h0w : 0 < 2 ^ P.w := by omega
  have h1w : 1 < 2 ^ P.w := by omega
  set s0 := startState [spanTbl, s, batchPtr, W, hp, ws, eCap, oldS, embH] mem₀ pos with hs0
  have hs0_0 : s0.regs 0 = spanTbl := by simp [s0, startState]
  have hs0_1 : s0.regs 1 = s := by simp [s0, startState]
  have hs0_2 : s0.regs 2 = batchPtr := by simp [s0, startState]
  have hs0_3 : s0.regs 3 = W := by simp [s0, startState]
  have hs0_4 : s0.regs 4 = hp := by simp [s0, startState]
  have hs0_5 : s0.regs 5 = ws := by simp [s0, startState]
  have hs0_6 : s0.regs 6 = eCap := by simp [s0, startState]
  have hs0_7 : s0.regs 7 = oldS := by simp [s0, startState]
  have hs0_8 : s0.regs 8 = embH := by simp [s0, startState]
  by_cases hb : mem₀ batchPtr = 0
  · -- The empty batch: nothing to do.
    have hb' : s0.mem batchPtr = 0 := hb
    have key : ∃ o st' c, Runs P.w p ω (asmFirstP4TaskStmt (bSpan + bsIdxOp0 + 1) fAfter) s0
        o st' c ∧ (o = .returned hp ∧ st'.mem = mem₀) ∧ 0 + c ≤ 10 := by
      unfold asmFirstP4TaskStmt
      wram_step
      wram_step
      · exact ⟨rfl, by simp [s0, startState]⟩
      · wram_cost
    obtain ⟨o, st', c, hr, ⟨ho, hm⟩, hc⟩ := key
    exact ⟨o, st', c, hr, fun _ => ⟨ho, hm, by omega⟩, fun h => absurd hb h⟩
  -- The update of the slot's spanner.
  have hb' : s0.mem batchPtr ≠ 0 := hb
  have hpre₀ := hpre hb
  have hUHcap := hUHcap hb
  have hDcap := hDcap hb
  have hRcap := hRcap hb
  have hWalkCap := hWalkCap hb
  have hspace := hspace hb
  have hpre₀' := hpre₀
  obtain ⟨b', bp', W', h', heq, -, -, -, hbp_le, -⟩ := hpre₀'
  simp only [List.cons.injEq, and_true] at heq
  obtain ⟨-, rfl, rfl, rfl⟩ := heq
  have hspan_lt : spanTbl + s < hp := bucket_slot_lt_of_foot hfoot hs
  have hsp_eq : (bucketSpannerDS P cap).space 1 S6 [spanTbl, s, batchPtr, W, hp] mem₀ =
      dsUpdateOpSpace P d [0, batchPtr, W, hp] mem₀ := by
    simp only [bucketSpannerDS, bucketUpdateSpace, List.getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some, hs, ↓reduceDIte]
    change (match S6 ⟨s, hs⟩ with
      | some s' => dsUpdateOpSpace P s' [0, batchPtr, W, hp] mem₀ | none => 0) = _
    rw [hSj]
  have hcost_eq : (bucketSpannerDS P cap).cost 1 S6 [spanTbl, s, batchPtr, W, hp] mem₀ =
      dsUpdateAmortCost P d [0, batchPtr, W, hp] mem₀ + 20 := by
    simp only [bucketSpannerDS, bucketUpdateCost, List.getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some, hs, ↓reduceDIte]
    change (match S6 ⟨s, hs⟩ with
      | some s' => dsUpdateAmortCost P s' [0, batchPtr, W, hp] mem₀ + 20 | none => 0) = _
    rw [hSj]
  have hW_le : W ≤ dsUpdateOpSpace P d [0, batchPtr, W, hp] mem₀ := by
    unfold dsUpdateOpSpace opWords
    simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
    omega
  have hhpW : hp + W < 2 ^ P.w := by omega
  have hargsW : ∀ a ∈ [spanTbl, s, batchPtr, W, hp], a < 2 ^ P.w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega
  have hImp := bucketSpannerDS_implements P cap hpS
  obtain ⟨bd, hbd, o₁, st₁, c₁, hrun₁, S', x', hrep', hpost', hresp', hc₁⟩ :=
    hImp.2.2 1 spanTbl S6 x6 [spanTbl, s, batchPtr, W, hp] mem₀ pos ω hargsW rfl hS6
      ⟨spanTbl, s, batchPtr, W, hp, rfl, hs, d, hSj, hpre₀⟩ hfoot hz (by rw [hsp_eq]; show hp + _ < _; omega)
  have hpost : BucketUpdatePost P cap S6 [spanTbl, s, batchPtr, W, hp] mem₀ S' st₁.mem := hpost'
  obtain ⟨hslot', s0', s1', hcurS', hS'eq, hdsPost⟩ := hpost
  have hcur : S6 ⟨s, hs⟩ = some s0' := hcurS'
  rw [hSj] at hcur
  obtain rfl := Option.some.inj hcur
  have hds : DSUpdatePost P d [0, batchPtr, W, hp] mem₀ s1' st₁.mem := hdsPost
  obtain ⟨hs1, ⟨uhOutPtr, uhOutWords, dOutPtr, rOutPtr, uhActual, dOut, rOut, hh0, -, -, hh3,
    hh4, hh5, hh6, hBat, hPerm, hHapp, hdNd, hdFs, hdAt, hrNd, hrFs, hrAt, hPl1, hPl2, hPl3,
    hPl4⟩, hT82⟩ := hds
  change st₁.mem (hp + W) = uhOutPtr at hh0
  change st₁.mem (hp + W + 3) = dOutPtr at hh3
  change st₁.mem (hp + W + 4) = dOut.length at hh4
  change st₁.mem (hp + W + 5) = rOutPtr at hh5
  change st₁.mem (hp + W + 6) = rOut.length at hh6
  change hp + W + 7 ≤ dOutPtr at hPl1
  subst hs1
  have hS' : S' = S6.set ⟨s, hs⟩
      (some ⟨d.G₀, d.Us ++ [(opBatch P d [0, batchPtr, W, hp] mem₀).1]⟩) := hS'eq
  subst hS'
  obtain ⟨hlo, hhi, hz₁, hfr₁, hft₁⟩ := hresp'
  change hp ≤ o₁.value at hlo
  change o₁.value ≤ hp + (bucketSpannerDS P cap).space 1 S6 [spanTbl, s, batchPtr, W, hp] mem₀
    at hhi
  rw [hsp_eq] at hhi
  change ∀ a < hp, ¬ bucketFoot spanTbl x6 a → st₁.mem a = mem₀ a at hfr₁
  change ∀ a, bucketFoot spanTbl x' a → bucketFoot spanTbl x6 a ∨ (hp ≤ a ∧ a < o₁.value)
    at hft₁
  rw [hcost_eq, bucketPhi_eq_specPhi hrep', bucketPhi_eq_specPhi hS6] at hc₁
  -- The facts for the work after the update, on the memory after the update.
  have hW₁ : Phase4WSAt st₁.mem ws eCap S := phase4WSAt_of_agree hW (fun a h1 h2 =>
    hfr₁ a (by omega) (fun hf => by rcases hSpanWs a hf with h | h <;> omega))
  have hEmb₁ : (embRep eCap).rep embH v y st₁.mem :=
    (embRep_local eCap embH v y mem₀ st₁.mem
      (fun a ha => (hfr₁ a (hEmbF a ha) (hDisj a ha)).symm)).1 hEmb
  have hOS₁ : ∀ e < eCap, st₁.mem (oldS + e) = if e ∈ OS then 1 else 0 := fun e he =>
    (hfr₁ _ (hoFoot e he).1 (hoFoot e he).2).trans (hOS e he)
  have hSj' : (S6.set ⟨s, hs⟩
      (some ⟨d.G₀, d.Us ++ [(opBatch P d [0, batchPtr, W, hp] mem₀).1]⟩)) ⟨s, hs⟩ =
      some ⟨d.G₀, d.Us ++ [(opBatch P d [0, batchPtr, W, hp] mem₀).1]⟩ := by
    simp [BucketSpannerState.set]
  have hsp : o₁.value + slotListWalkWords P (S6.set ⟨s, hs⟩
      (some ⟨d.G₀, d.Us ++ [(opBatch P d [0, batchPtr, W, hp] mem₀).1]⟩)) s
      (p4TaskScan P ⟨d.G₀, d.Us ++ [(opBatch P d [0, batchPtr, W, hp] mem₀).1]⟩ OS uhActual dOut
        rOut S).copyBuf < 2 ^ P.w := by
    have := slotListWalkWords_le_sum P (S6.set ⟨s, hs⟩
      (some ⟨d.G₀, d.Us ++ [(opBatch P d [0, batchPtr, W, hp] mem₀).1]⟩)) s
      (p4TaskScan_copyBuf_nodup P ⟨d.G₀, d.Us ++ [(opBatch P d [0, batchPtr, W, hp] mem₀).1]⟩ OS
        uhActual dOut rOut S)
      (fun e he => mem_p4TaskScan_copyBuf he)
    omega
  obtain ⟨o₂, st₂, c₂, hrun₂, hpost₂, hc₂⟩ := asmFirstP4After_runs (pos := st₁.pos) (ω := ω)
    (hOut := hp + W) (h := o₁.value)
    hfUH hfD hfR hfDl hfC hfEdge hfPush hfMark hcopy hread hs hSj' hw16 hW₁ hrep' hEmb₁ hOS₁
    hh0 hh3 hh4 hh5 hh6 hBat hdAt hrAt hPl1 hPl2 hPl3 (by omega)
    (fun u hu => hUHcap u (hPerm.subset hu))
    (fun e he => hDcap e (by rw [← hdFs]; exact List.mem_toFinset.mpr he))
    (fun e he => hRcap e (by rw [← hrFs]; exact List.mem_toFinset.mpr he))
    heCap hWalkCap (by omega) (by omega)
    (fun a ha => by
      rcases hft₁ a ha with h | ⟨_, h⟩
      · exact lt_of_lt_of_le (hfoot a h) hlo
      · exact h)
    (fun a ha => lt_of_lt_of_le (hEmbF a ha) hlo)
    (fun a ha => by
      rcases hft₁ a ha with h | ⟨h, _⟩
      · exact hSpanWs a h
      · right; omega)
    hEmbWs
    (fun a ha hb => by
      rcases hft₁ a hb with h | ⟨h, _⟩
      · exact hDisj a ha h
      · have := hEmbF a ha; omega)
    ho_disj ho_w hz₁ hsp
  -- The run of the task.
  have key : ∃ o st' c, Runs P.w p ω (asmFirstP4TaskStmt (bSpan + bsIdxOp0 + 1) fAfter) s0
      o st' c ∧
      P4AfterPost P (S6.set ⟨s, hs⟩
          (some ⟨d.G₀, d.Us ++ [(opBatch P d [0, batchPtr, W, hp] mem₀).1]⟩)) x' spanTbl s ws
        eCap embH o₁.value ⟨d.G₀, d.Us ++ [(opBatch P d [0, batchPtr, W, hp] mem₀).1]⟩ OS uhActual
        dOut rOut S v y st₁.mem o st' ∧
      0 + c ≤ c₁ + c₂ + 40 := by
    unfold asmFirstP4TaskStmt
    wram_step
    refine runs_seq_callRuns_le (by eval_expr) hbd hrun₁ ?_
    refine runs_seq_callRuns_le (by eval_expr) hfAfter hrun₂ ?_
    wram_step
    · have hv : Outcome.returned o₂.value = o₂ := by rw [hpost₂.1]; rfl
      rw [hv]
      exact hpost₂
    · wram_cost
  obtain ⟨o, st', c, hr, hq, hc⟩ := key
  refine ⟨o, st', c, hr, fun h => absurd h hb, fun _ => ⟨o₁.value, st₁.mem, x', uhActual, dOut,
    rOut, hlo, hhi, hfr₁, hft₁, hPerm, hHapp, hdNd, hdFs, hrNd, hrFs, hT82, hq, ?_⟩⟩
  omega

end

end MinCostFlow.SparseCore.Program
