module

public import MinCostFlow.MinRatio.WireTreeSync
public import MinCostFlow.MinRatio.WireChainCoreBatch
import WordRAM.Tactic

/-!
# Deferred-push path-tree sync invariant (`WireChainCoreSyncDefs`)

Provides `WireSyncDeferInv`, a copy of `WireSyncInv` parameterized by a set `deferSet : Finset ℕ`
of off-tree edges whose `offReadyList` push is deferred until after `wireTreeSyncLoop` completes
(via `wireRebuildOffReadyBody` in Branch A or `wirePushReadyBatchBody` in Branch B).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Bundle DynSpanner.Program IPM.Machine

/-- State invariant of `wireTreeSyncLoop` with `offReadyList` membership deferred on `deferSet`. -/
@[expose] def WireSyncDeferInv {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    (deferSet : Finset ℕ)
    (root editPtr heap0 : ℕ) (memStart : ℕ → ℕ)
    (G0 oldF _newF : MGraph) (edits : List TreeChange)
    (tok : SolverToken cfg L Rcore) (canonVal : ℕ → PathEdgeValue) (B R : ℤ)
    (done rem : List TreeChange)
    (curTree : PathTreeState)
    (curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ)
    (curHeap curOffCnt : ℕ) (st : State) : Prop :=
  let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
  let curE := applyTreeChanges oldF.E done
  done ++ rem = edits ∧
  st.regs 0 = tok.treeHeap ∧ st.regs 1 = root ∧ st.regs 2 = L ∧
  st.regs 3 = curHeap ∧ st.regs 6 = editPtr + 2 * done.length ∧
  st.regs 18 = rem.length ∧
  st.regs 9 = dgETailSlotBase tok.rootGraph G0.n tok.rootECap ∧
  st.regs 10 = dgEHeadSlotBase tok.rootGraph G0.n tok.rootECap ∧
  st.regs 11 = dgIntToExtBase tok.rootGraph G0.n ∧
  st.regs 19 = tok.slots ∧ st.regs 20 = tok.names ∧ st.regs 22 = tok.edgeRecords ∧
  st.regs 23 = tok.edgeThresholds ∧ st.regs 24 = tok.slotThresholds ∧
  st.regs 25 = tok.offReadyList ∧ st.regs 26 = tok.inOffReady ∧
  heap0 ≤ curHeap ∧ curHeap ≤ heap0 + done.length * wireTreeSyncEditSpace L ∧
  ZeroFrom st.mem curHeap ∧
  (∀ a, Rtree.foot tok.treeHeap curTreeTok a →
    Rtree.foot tok.treeHeap tok.treeTok a ∨ (heap0 ≤ a ∧ a < curHeap)) ∧
  (∀ a < heap0, a ≠ root + 11 → tok.tag a ≠ 9 → tok.tag a ≠ 10 → tok.tag a ≠ 11 →
    tok.tag a ≠ 13 → tok.tag a ≠ 14 → tok.tag a ≠ 15 → tok.tag a ≠ 16 →
    st.mem a = memStart a) ∧
  curTree.n = G0.n ∧
  (∃ curTrees curFree curDepth,
    LctInvWith pathPayload curTree curTrees curFree curDepth ∧
    PathTreeNumericInv curTree curTrees B R ∧
    TreeEditNamedSlots curTree curTrees { G0 with E := curE }
      (fun ei => st.mem (tok.slots + ei)) (fun sl => st.mem (tok.names + sl)) ∧
    TreeEditLiveAccounts curTree curTrees { G0 with E := curE }
      (fun ei => st.mem (tok.slots + ei)) canonVal) ∧
  Rtree.rep tok.treeHeap curTree curTreeTok st.mem ∧
  (∀ ei ∈ curE, st.mem (tok.slotThresholds + st.mem (tok.slots + ei)) =
    st.mem (tok.edgeThresholds + ei)) ∧
  (∀ ei ∈ G0.E, ei ∉ curE → st.mem (tok.slots + ei) = 0) ∧
  (∀ ei ∈ G0.E, ei ∉ curE →
    PathEdgeAt st.mem (st.mem (tok.edgeRecords + ei)) 4 L (some (canonVal ei))) ∧
  (∀ ei ∈ G0.E, ei ∉ curE → ei ∉ deferSet → 0 ≤ (canonVal ei).detector →
    st.mem (tok.inOffReady + ei) = 1) ∧
  (∀ ei ∈ G0.E, ei ∉ curE →
    (ei ∈ oldF.E →
      heap0 ≤ st.mem (tok.edgeRecords + ei) ∧
      st.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ curHeap ∧
      ∀ a, st.mem (tok.edgeRecords + ei) ≤ a →
        a < st.mem (tok.edgeRecords + ei) + (2 + 4 * L) →
        ¬ Rtree.foot tok.treeHeap curTreeTok a) ∧
    (ei ∉ oldF.E → st.mem (tok.edgeRecords + ei) = memStart (tok.edgeRecords + ei))) ∧
  (∀ e₁ ∈ G0.E, ∀ e₂ ∈ G0.E, e₁ ≠ e₂ → e₁ ∉ curE → e₂ ∉ curE →
    st.mem (tok.edgeRecords + e₁) + (2 + 4 * L) ≤ st.mem (tok.edgeRecords + e₂) ∨
    st.mem (tok.edgeRecords + e₂) + (2 + 4 * L) ≤ st.mem (tok.edgeRecords + e₁)) ∧
  st.mem (root + 11) = curOffCnt ∧
  OffReadyInv st.mem curOffCnt tok.offReadyList tok.inOffReady tok.intCap

theorem wireSyncDefer_step_wrap {w L drainUnit : ℕ} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    {p : Program} {ω : ℕ → Bool} {fmt : Num.Format w}
    {initTree : ℕ} {opTree : ℕ → ℕ} {bind canonCopy isNeg : ℕ}
    {root editPtr heap0 : ℕ} {memStart : ℕ → ℕ}
    {G0 oldF newF : MGraph} {edits done rem : List TreeChange} {ch : TreeChange}
    {tok : SolverToken cfg L Rcore} {canonVal : ℕ → PathEdgeValue} {B R : ℤ}
    {curTree : PathTreeState}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    {deferSet : Finset ℕ} {curHeap curOffCnt tagVal e : ℕ} {st mid : State} {cBranch : ℕ}
    (ctx : WireSyncCtx w L drainUnit cfg Rcore p fmt initTree opTree bind canonCopy isNeg
      root editPtr heap0 memStart G0 oldF newF edits tok canonVal B R)
    (hinv : WireSyncDeferInv deferSet root editPtr heap0 memStart G0 oldF newF edits tok canonVal B R
      done (ch :: rem) curTree curTreeTok curHeap curOffCnt st)
    (htw : treeEditWords ch = [tagVal, e]) (heG : e ∈ G0.E)
    (hbr :
      let s1 := { st with regs := Function.update st.regs 7 tagVal }
      let s2 := { s1 with regs := Function.update s1.regs 8 e }
      let s3 := { s2 with regs := Function.update s2.regs 12 (G0.tail e + 1) }
      let s4 := { s3 with regs := Function.update s3.regs 13 (G0.head e + 1) }
      Runs w p ω (if tagVal = 0 then wireTreeSyncDelete (opTree 4) (opTree 1) canonCopy isNeg
        else wireTreeSyncInsert (opTree 0) bind) s4 .normal mid cBranch)
    (h6m : mid.regs 6 = editPtr + 2 * done.length) (h18m : mid.regs 18 = rem.length + 1) :
    let out := { mid with regs := Function.update (Function.update mid.regs 6
      (editPtr + 2 * (done.length + 1))) 18 rem.length }
    Runs w p ω (wireTreeSyncStep (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg)
      st .normal out (cBranch + 44) := by
  obtain ⟨happ, _, _, _, _, hr6, _, hr9, hr10, hr11, _, _, _, _, _, _, _, _, _, _, _, hFrame, _⟩ := hinv
  have hlenEq : done.length + (rem.length + 1) = edits.length := by
    have := congrArg List.length happ; simp at this; omega
  have hw1 : 1 < 2 ^ w := by have := ctx.hw11; omega
  have hw2 : 2 < 2 ^ w := by have := ctx.hw11; omega
  have htagLt {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) : a < heap0 := ctx.tags.1 a (ht ▸ hv)
  have hwordsCur : ListAt st.mem (editPtr + 2 * done.length) [tagVal, e] := by
    have hsplit : edits.flatMap treeEditWords =
        done.flatMap treeEditWords ++ treeEditWords ch ++ rem.flatMap treeEditWords := by
      rw [← happ, List.flatMap_append, List.flatMap_cons, List.append_assoc]
    have hat := ctx.editsAt; rw [TreeEditsAt, hsplit] at hat
    have h2 := (listAt_append.mp (listAt_append.mp hat).1).2
    rw [treeEditWords_length, htw] at h2
    refine h2.congr fun a ha1 ha2 => ?_
    have hEd := ctx.editsTag0 a (by omega) (by simp at ha2; omega)
    exact hFrame a (by have := ctx.editsEnd; simp at ha2; omega) hEd.2
      (by rw [hEd.1]; decide) (by rw [hEd.1]; decide) (by rw [hEd.1]; decide)
      (by rw [hEd.1]; decide) (by rw [hEd.1]; decide) (by rw [hEd.1]; decide) (by rw [hEd.1]; decide)
  have hDG : DynGraphAt st.mem tok.rootGraph G0.n tok.rootECap G0 :=
    ctx.rootGraph.of_agree fun a ha1 ha2 => by
      have ht20 := ctx.tags.2.2.2.2.2.2.2.2.2.2.2 a ha1 ha2
      have hneR : a ≠ root + 11 := fun he => by rw [he, ctx.tags.2.1 11 (by omega)] at ht20; omega
      exact hFrame a (htagLt ht20 (by decide)) hneR (by rw [ht20]; decide)
        (by rw [ht20]; decide) (by rw [ht20]; decide) (by rw [ht20]; decide)
        (by rw [ht20]; decide) (by rw [ht20]; decide) (by rw [ht20]; decide)
  have hDGroom : tok.rootGraph + dynGraphSize G0.n tok.rootECap ≤ 2 ^ w := by
    have hsz : 0 < dynGraphSize G0.n tok.rootECap := by unfold dynGraphSize; omega
    have hlast := htagLt (ctx.tags.2.2.2.2.2.2.2.2.2.2.2
      (tok.rootGraph + dynGraphSize G0.n tok.rootECap - 1) (by omega) (by omega)) (by decide)
    have := ctx.room; omega
  have ht0 : st.mem (editPtr + 2 * done.length) = tagVal := by simpa using hwordsCur 0 (by simp)
  have he1 : st.mem (editPtr + 2 * done.length + 1) = e := hwordsCur 1 (by simp)
  have haddr1 : editPtr + 2 * done.length + 1 < 2 ^ w := by have := ctx.editsEnd; have := ctx.room; omega
  have hEp := TreeEditEndpointAt.of_graph hDG heG
  have htailSlotW : dgETailSlotBase tok.rootGraph G0.n tok.rootECap + e < 2 ^ w := by
    simp only [dgETailSlotBase, dynGraphSize] at hDGroom ⊢; have := hEp.edgeBound; omega
  have hheadSlotW : dgEHeadSlotBase tok.rootGraph G0.n tok.rootECap + e < 2 ^ w := by
    simp only [dgEHeadSlotBase, dynGraphSize] at hDGroom ⊢; have := hEp.edgeBound; omega
  have htailInvW : dgIntToExtBase tok.rootGraph G0.n +
      st.mem (dgETailSlotBase tok.rootGraph G0.n tok.rootECap + e) < 2 ^ w := by
    simp only [dgIntToExtBase, dynGraphSize] at hDGroom ⊢; have := hEp.tailSlotBound; omega
  have hheadInvW : dgIntToExtBase tok.rootGraph G0.n +
      st.mem (dgEHeadSlotBase tok.rootGraph G0.n tok.rootECap + e) < 2 ^ w := by
    simp only [dgIntToExtBase, dynGraphSize] at hDGroom ⊢; have := hEp.headSlotBound; omega
  have hu1W : G0.tail e + 1 < 2 ^ w := by have := (ctx.vtxE e heG).1; have := ctx.nW; omega
  have hv1W : G0.head e + 1 < 2 ^ w := by have := (ctx.vtxE e heG).2; have := ctx.nW; omega
  let s1 := { st with regs := Function.update st.regs 7 tagVal }
  let s2 := { s1 with regs := Function.update s1.regs 8 e }
  let s3 := { s2 with regs := Function.update s2.regs 12 (G0.tail e + 1) }
  let s4 := { s3 with regs := Function.update s3.regs 13 (G0.head e + 1) }
  have r1 : Runs w p ω (.assign 7 (.load (.reg 6))) st .normal s1 3 :=
    runs_assign_iff.mpr ⟨tagVal, by simp [Expr.eval, hr6, ht0], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 6) (.const 1)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨e, by simp [Expr.eval, BinOp.eval, s1, hr6, hw1, haddr1, he1], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 12 (.bin .add (.load (.bin .add (.reg 11)
      (.load (.bin .add (.reg 9) (.reg 8))))) (.const 1))) s2 .normal s3 10 :=
    runs_assign_iff.mpr ⟨G0.tail e + 1, by
      simp [Expr.eval, BinOp.eval, s2, s1, hr9, hr11, htailSlotW, htailInvW, hEp.tailName, hw1, hu1W],
      rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 13 (.bin .add (.load (.bin .add (.reg 11)
      (.load (.bin .add (.reg 10) (.reg 8))))) (.const 1))) s3 .normal s4 10 :=
    runs_assign_iff.mpr ⟨G0.head e + 1, by
      simp [Expr.eval, BinOp.eval, s3, s2, s1, hr10, hr11, hheadSlotW, hheadInvW, hEp.headName, hw1, hv1W],
      rfl, rfl, rfl⟩
  have rCond : Runs w p ω (.cond (.reg 7) (wireTreeSyncInsert (opTree 0) bind)
      (wireTreeSyncDelete (opTree 4) (opTree 1) canonCopy isNeg)) s4 .normal mid (cBranch + 2) :=
    runs_cond_iff.mpr ⟨tagVal, cBranch, by simp [Expr.eval, s4, s3, s2, s1], hbr, by simp [Expr.size]; omega⟩
  let mid1 := { mid with regs := Function.update mid.regs 6 (editPtr + 2 * (done.length + 1)) }
  let out := { mid with regs := Function.update (Function.update mid.regs 6
    (editPtr + 2 * (done.length + 1))) 18 rem.length }
  have h6W : editPtr + 2 * (done.length + 1) < 2 ^ w := by have := ctx.editsEnd; have := ctx.room; omega
  have h18W : rem.length < 2 ^ w := by have := ctx.editsEnd; have := ctx.room; omega
  have rA : Runs w p ω (.assign 6 (.bin .add (.reg 6) (.const 2))) mid .normal mid1 4 :=
    runs_assign_iff.mpr ⟨editPtr + 2 * (done.length + 1), by
      simp [Expr.eval, BinOp.eval, h6m, hw2, show editPtr + 2 * done.length + 2 =
        editPtr + 2 * (done.length + 1) by omega, h6W], rfl, rfl, rfl⟩
  have rB : Runs w p ω (.assign 18 (.bin .sub (.reg 18) (.const 1))) mid1 .normal out 4 :=
    runs_assign_iff.mpr ⟨rem.length, by simp [Expr.eval, BinOp.eval, mid1, h18m, hw1, h18W], rfl, rfl, rfl⟩
  unfold wireTreeSyncStep
  exact runs_seq_iff.mpr (Or.inr ⟨s1, 3, cBranch + 40, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 5, cBranch + 34, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 10, cBranch + 23, r3,
        runs_seq_iff.mpr (Or.inr ⟨s4, 10, cBranch + 12, r4,
          runs_seq_iff.mpr (Or.inr ⟨mid, cBranch + 2, 9, rCond,
            runs_seq_iff.mpr (Or.inr ⟨mid1, 4, 4, rA, rB, rfl⟩), by omega⟩), by omega⟩),
        by omega⟩), by omega⟩), by omega⟩)

/-- Syntactic predicate stating that statement `s` never writes to any register `≥ lo`. -/
@[expose] def stmtNoWriteGe (lo : ℕ) : Stmt → Prop
  | .nop => True
  | .assign r _ => r < lo
  | .store _ _ => True
  | .seq s₁ s₂ => stmtNoWriteGe lo s₁ ∧ stmtNoWriteGe lo s₂
  | .cond _ s₁ s₂ => stmtNoWriteGe lo s₁ ∧ stmtNoWriteGe lo s₂
  | .loop _ s => stmtNoWriteGe lo s
  | .call r _ _ => r < lo
  | .ret _ => True
  | .rand r => r < lo

/-- Any statement with `stmtNoWriteGe lo s` preserves all registers `r ≥ lo` across execution. -/
theorem runs_regs_ge_of_noWriteGe {w lo : ℕ} {p : Program} {ω : ℕ → Bool}
    {s : Stmt} {st out : State} {o : Outcome} {c : ℕ}
    (hr : Runs w p ω s st o out c) (hnw : stmtNoWriteGe lo s) :
    ∀ r, lo ≤ r → out.regs r = st.regs r := by
  obtain ⟨f, hf⟩ := hr
  revert hnw
  induction f generalizing s st out o c with
  | zero => simp [exec] at hf
  | succ f ih =>
    intro hnw
    cases s with
    | nop => simp [exec] at hf; rcases hf with ⟨_, rfl, _⟩; intro _ _; rfl
    | assign reg e =>
      dsimp only [stmtNoWriteGe] at hnw
      simp only [exec] at hf
      cases he : e.eval w st <;> simp [he] at hf
      rcases hf with ⟨_, rfl, _⟩; intro r hr; exact Function.update_of_ne (by omega) _ _
    | store a e =>
      simp only [exec] at hf
      cases ha : a.eval w st <;> simp [ha] at hf
      cases he : e.eval w st <;> simp [he] at hf
      rcases hf with ⟨_, rfl, _⟩; intro _ _; rfl
    | rand reg =>
      dsimp only [stmtNoWriteGe] at hnw
      simp only [exec] at hf; rcases hf with ⟨_, rfl, _⟩
      intro r hr; exact Function.update_of_ne (by omega) _ _
    | ret e =>
      simp only [exec] at hf
      cases he : e.eval w st <;> simp [he] at hf
      rcases hf with ⟨_, rfl, _⟩; intro _ _; rfl
    | seq s₁ s₂ =>
      simp only [exec] at hf
      cases h1 : exec w p ω f s₁ st with
      | none => simp [h1] at hf
      | some res₁ =>
        rcases res₁ with ⟨o₁, st₁, c₁⟩; simp only [h1] at hf
        cases o₁ with
        | returned v => simp at hf; rcases hf with ⟨_, rfl, _⟩; exact ih h1 hnw.1
        | normal =>
          cases h2 : exec w p ω f s₂ st₁ with
          | none => simp [h2] at hf
          | some res₂ =>
            rcases res₂ with ⟨o₂, st₂, c₂⟩; simp [h2] at hf
            rcases hf with ⟨_, rfl, _⟩
            intro r hr; exact (ih h2 hnw.2 r hr).trans (ih h1 hnw.1 r hr)
    | cond e s₁ s₂ =>
      simp only [exec] at hf
      cases he : e.eval w st <;> simp [he] at hf
      rename_i v
      cases hbr : exec w p ω f (if v = 0 then s₂ else s₁) st with
      | none => simp [hbr] at hf
      | some res =>
        rcases res with ⟨o', st', c'⟩; simp [hbr] at hf
        rcases hf with ⟨_, rfl, _⟩
        split_ifs at hbr with hv
        · exact ih hbr hnw.2
        · exact ih hbr hnw.1
    | loop e body =>
      simp only [exec] at hf
      cases he : e.eval w st <;> simp [he] at hf
      rename_i v
      by_cases hv : v = 0
      · simp [hv] at hf; rcases hf with ⟨_, rfl, _⟩; intro _ _; rfl
      · simp only [hv, ↓reduceIte] at hf
        cases hb : exec w p ω f body st with
        | none => simp [hb] at hf
        | some res₁ =>
          rcases res₁ with ⟨o₁, st₁, c₁⟩; simp only [hb] at hf
          cases o₁ with
          | returned u => simp at hf; rcases hf with ⟨_, rfl, _⟩; exact ih hb hnw
          | normal =>
            cases hl : exec w p ω f (.loop e body) st₁ with
            | none => simp [hl] at hf
            | some res₂ =>
              rcases res₂ with ⟨o₂, st₂, c₂⟩; simp [hl] at hf
              rcases hf with ⟨_, rfl, _⟩
              intro r hr; exact (ih hl hnw r hr).trans (ih hb hnw r hr)
    | call reg fn args =>
      dsimp only [stmtNoWriteGe] at hnw
      simp only [exec] at hf
      cases ha : evalArgs w st args <;> simp [ha] at hf
      cases hp : p.procs[fn]? <;> simp [hp] at hf
      split at hf
      · cases hf
      · cases hf
        intro r hr; exact Function.update_of_ne (by omega) _ _

theorem shiftTermSetupLoop_noWriteGe70 : stmtNoWriteGe 70 shiftTermSetupLoop := by
  simp [shiftTermSetupLoop, stmtNoWriteGe]

theorem wireTreeSyncLoop_noWriteGe70 (expose cut link bind canonCopy isNeg : ℕ) :
    stmtNoWriteGe 70 (wireTreeSyncLoop expose cut link bind canonCopy isNeg) := by
  simp [wireTreeSyncLoop, wireTreeSyncStep, wireTreeSyncDelete, wireTreeSyncInsert, stmtNoWriteGe]

/-- The empty `MGraph` represented by 4 zero words `[0, 0, 0, 0]`. -/
@[expose] def emptyZeroGraph : MGraph :=
  { V := ∅, E := ∅, tail := fun _ => 0, head := fun _ => 0 }

theorem emptyZeroGraph_dynGraphAt {mem : ℕ → ℕ} {p : ℕ}
    (hz : ∀ j < 4, mem (p + j) = 0) :
    DynGraphAt mem p 0 0 emptyZeroGraph := by
  refine ⟨fun _ h => by simp [emptyZeroGraph] at h,
    fun _ h => by simp [emptyZeroGraph] at h,
    fun _ h => by simp [emptyZeroGraph] at h,
    by simpa [dgVCapOff] using hz 0 (by omega),
    by simpa [dgECapOff] using hz 1 (by omega),
    by simpa [dgNOff, emptyZeroGraph, MGraph.n] using hz 2 (by omega),
    by simpa [dgMOff, emptyZeroGraph, MGraph.m] using hz 3 (by omega),
    fun _ hv => by omega,
    ⟨[], by simp [emptyZeroGraph, MGraph.n], List.nodup_nil, by simp [emptyZeroGraph],
      fun _ h => by simp at h, fun _ h => by simp at h⟩,
    fun _ hv => by simp [emptyZeroGraph] at hv,
    fun _ hv => by simp [emptyZeroGraph] at hv,
    fun _ he => by omega,
    ⟨[], by simp [emptyZeroGraph, MGraph.m], List.nodup_nil, by simp [emptyZeroGraph],
      fun _ h => by simp at h, fun _ h => by simp at h⟩,
    fun _ he => by simp [emptyZeroGraph] at he,
    ⟨fun _ => [], fun _ hv => by omega⟩⟩

theorem graphListEdgeUnion_replicate_empty (cnt : ℕ) :
    graphListEdgeUnion (List.replicate cnt emptyZeroGraph) = ∅ := by
  induction cnt with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, graphListEdgeUnion, List.foldl_cons]
    have h0 : (∅ : Finset ℕ) ∪ emptyZeroGraph.E = ∅ := by simp [emptyZeroGraph]
    rw [h0]; exact ih

theorem graphListEdgeSum_replicate_empty (cnt : ℕ) :
    graphListEdgeSum (List.replicate cnt emptyZeroGraph) = 0 := by
  induction cnt with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ]; unfold graphListEdgeSum at ih ⊢
    simp [emptyZeroGraph, MGraph.m]

theorem smallBatchAt_words_le_edgeOnly {mem : ℕ → ℕ} {a bW : ℕ} {G : MGraph} {U : List Update}
    (hB : SmallBatchAt mem a G U bW) (hEdge : ∀ u ∈ U, IsEdgeUpdate u) :
    bW ≤ 4 * U.length + 1 := by
  suffices ∀ {a' w' : ℕ} {G' : MGraph} {U' : List Update},
      BatchBodyAt mem a' G' U' w' → (∀ u ∈ U', IsEdgeUpdate u) → w' ≤ 4 * U'.length by
    obtain ⟨_, _, hBody⟩ := hB.1
    have h := this hBody hEdge
    omega
  intro a' w' G' U'
  induction U' generalizing a' w' G' with
  | nil => intro h _; exact Nat.le_of_eq h
  | cons u us ih =>
    intro hBody hE
    obtain ⟨len, hle, hU, hRest⟩ := hBody
    have hu := hE u List.mem_cons_self
    have hR := ih hRest (fun v hv => hE v (List.mem_cons_of_mem _ hv))
    cases u with
    | insert _ _ _ => obtain ⟨rfl, _⟩ := hU; simp only [List.length_cons]; omega
    | delete _ => obtain ⟨rfl, _⟩ := hU; simp only [List.length_cons]; omega
    | split _ _ _ _ => exact hu.elim

end MinCostFlow.MinRatio
