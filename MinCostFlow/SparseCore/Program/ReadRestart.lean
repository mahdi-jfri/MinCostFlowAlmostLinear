module

public import MinCostFlow.SparseCore.Program.ReadRestartAdd
public import MinCostFlow.SparseCore.Program.RestartIface

import MinCostFlow.SparseCore.Program.SpanBucketInit
import WordRAM.Tactic

/-!
# Restart procedure of piece P10 and its `ScurRebuildAt` interface (`ReadRestart`)

Assembles `readRestartStmt` (`[r, spanTbl, n, slotsPtr, b4, j, h]`): loads `sPtr`, `gPtr` from
`r + 5`, `r + 6`; copies `slots` to `[h, h + n)` (`copyListStmt`); deletes `slotsGE SP S6 slots`
from `S` (`restartDelSlotsStmt`); and inserts each listed slot's `H_s` edges at core ends via P4's
root query `Q` (`restartAddSlotEdgesStmt`). Proves `readRestart_core_runs`,
`readRestart_branch_clause`, and `readRestart_scurRebuildAt` (meeting `ScurRebuildAt` of
`RestartIface.lean`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.MinRatio MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program MinCostFlow.SparseCore.Program.Restart MinCostFlow.Chain

/-! ## Procedure definitions -/

/-- The restart procedure `[r, spanTbl, n, slotsPtr, b4, j, h]`: rebuilds `S` in place from the
bucket spanners of the `n` listed slots and P4's root query. Returns the new heap pointer. -/
def readRestartStmt (fCopy fDelSlots fAddSlotEdges : ℕ) : Stmt :=
  .assign 7 (.load (.bin .add (.reg 0) (.const 5))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const 6))) ;;
  .call 9 fCopy [.reg 6, .reg 3, .reg 2] ;;
  .assign 10 (.bin .add (.reg 6) (.reg 2)) ;;
  .call 9 fDelSlots [.reg 7, .reg 1, .reg 6, .reg 2] ;;
  forRange 11 (.const 0) (.reg 2)
    (.assign 12 (.load (.bin .add (.reg 6) (.reg 11))) ;;
     .assign 13 (.load (.bin .add (.reg 1) (.reg 12))) ;;
     .assign 14 (.load (.bin .add (.reg 13) (.const dsVCapOff))) ;;
     .assign 15 (.load (.bin .add (.reg 13) (.const dsECapOff))) ;;
     .assign 16 (.bin .add (.bin .add (.reg 13) (.const dsHdrSize))
       (.bin .add (.const 4)
         (.bin .add (.bin .mul (.const 7) (.reg 14)) (.bin .mul (.const 9) (.reg 15))))) ;;
     .call 10 fAddSlotEdges [.reg 7, .reg 8, .reg 16, .reg 4, .reg 5, .reg 10]) ;;
  .ret (.reg 10)

def readRestartIdxCopy : ℕ := 0
def readRestartIdxDel : ℕ := 1
def readRestartIdxAdd : ℕ := 2
def readRestartIdxMain : ℕ := 3

/-- The four deterministic procedures of the restart module anchored at `bSelf`. -/
def readRestartProcs (bOps bEdge bLoop fRoot bSelf : ℕ) : List Stmt :=
  [copyListStmt,
   restartDelSlotsStmt bLoop,
   restartAddSlotEdgesStmt bOps bEdge fRoot,
   readRestartStmt (bSelf + readRestartIdxCopy) (bSelf + readRestartIdxDel)
     (bSelf + readRestartIdxAdd)]

theorem readRestartProcs_length (bOps bEdge bLoop fRoot bSelf : ℕ) :
    (readRestartProcs bOps bEdge bLoop fRoot bSelf).length = 4 := rfl

theorem readRestartProcs_noRand (bOps bEdge bLoop fRoot bSelf : ℕ) :
    ∀ s ∈ readRestartProcs bOps bEdge bLoop fRoot bSelf, s.NoRand := by
  intro s hs
  simp only [readRestartProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact copyListStmt_noRand
  · exact restartDelSlotsStmt_noRand bLoop
  · exact restartAddSlotEdgesStmt_noRand bOps bEdge fRoot
  · simp [readRestartStmt, forRange, forUp, Stmt.NoRand]

/-! ## Prefix-graph helper for the add-slots loop -/

/-- The intermediate `S` graph after removing `slotsGE SP S6 slots` and inserting the spanner
edges of `slots.take i`. -/
noncomputable def rebuildPrefixS (SP : DSParams) {cap : ℕ} (v : ReadView)
    (S6 : BucketSpannerState cap) (slots : List ℕ) (i : ℕ) : MGraph :=
  open Classical in
  let baseE := v.S.E \ slotsGE SP S6 slots
  let add := (slotsHE SP S6 (slots.take i) ∩ v.G.E).filter fun e =>
    (coreGraph v.G v.lsf).tail e ∈ v.S.V ∧ (coreGraph v.G v.lsf).head e ∈ v.S.V
  { V := v.S.V
    E := baseE ∪ add
    tail := fun e => if e ∈ add then (coreGraph v.G v.lsf).tail e else v.S.tail e
    head := fun e => if e ∈ add then (coreGraph v.G v.lsf).head e else v.S.head e }

private theorem rebuildPrefixS_zero (SP : DSParams) {cap : ℕ} (v : ReadView)
    (S6 : BucketSpannerState cap) (slots : List ℕ) :
    SameGraph { v.S with E := v.S.E \ slotsGE SP S6 slots } (rebuildPrefixS SP v S6 slots 0) := by
  refine ⟨rfl, ?_, fun e _ => ?_⟩
  · simp [rebuildPrefixS, slotsHE]
  · simp [rebuildPrefixS, slotsHE]

private theorem rebuildPrefixS_end {SP : DSParams} {cap : ℕ} {v : ReadView}
    {S6 : BucketSpannerState cap} {slots : List ℕ}
    (hsub : slotsHE SP S6 slots ⊆ slotsGE SP S6 slots) :
    SameGraph (rebuildPrefixS SP v S6 slots slots.length) (v.rebuild SP S6 slots).S := by
  have hun : slotsGE SP S6 slots ∪ slotsHE SP S6 slots = slotsGE SP S6 slots :=
    Finset.union_eq_left.mpr hsub
  refine ⟨rfl, ?_, fun e _ => ?_⟩
  · simp [rebuildPrefixS, ReadView.rebuild, ReadView.rebuildS, hun]
  · simp [rebuildPrefixS, ReadView.rebuild, ReadView.rebuildS]

private theorem rebuildPrefixS_step {SP : DSParams} {cap : ℕ} {v : ReadView}
    {S6 : BucketSpannerState cap} {slots : List ℕ} {i : ℕ} (hi : i < slots.length) :
    let Si := rebuildPrefixS SP v S6 slots i
    let add1 := (slotHE SP S6 slots[i] ∩ v.G.E).filter fun e =>
      (coreGraph v.G v.lsf).tail e ∈ Si.V ∧ (coreGraph v.G v.lsf).head e ∈ Si.V
    SameGraph
      { V := Si.V, E := Si.E ∪ add1,
        tail := fun e => if e ∈ add1 then (coreGraph v.G v.lsf).tail e else Si.tail e,
        head := fun e => if e ∈ add1 then (coreGraph v.G v.lsf).head e else Si.head e }
      (rebuildPrefixS SP v S6 slots (i + 1)) := by
  classical
  intro Si add1
  have hHE_succ : slotsHE SP S6 (slots.take (i + 1)) =
      slotsHE SP S6 (slots.take i) ∪ slotHE SP S6 slots[i] := by
    rw [List.take_succ_eq_append_getElem hi]
    ext e
    simp only [slotsHE, Finset.mem_biUnion, List.mem_toFinset, List.mem_append, List.mem_singleton,
      Finset.mem_union]
    constructor
    · rintro ⟨s, hs | rfl, hes⟩
      · exact Or.inl ⟨s, hs, hes⟩
      · exact Or.inr hes
    · rintro (⟨s, hs, hes⟩ | hes)
      · exact ⟨s, Or.inl hs, hes⟩
      · exact ⟨slots[i], Or.inr rfl, hes⟩
  set add0 := (slotsHE SP S6 (slots.take i) ∩ v.G.E).filter fun e =>
    (coreGraph v.G v.lsf).tail e ∈ v.S.V ∧ (coreGraph v.G v.lsf).head e ∈ v.S.V
  set addNext := (slotsHE SP S6 (slots.take (i + 1)) ∩ v.G.E).filter fun e =>
    (coreGraph v.G v.lsf).tail e ∈ v.S.V ∧ (coreGraph v.G v.lsf).head e ∈ v.S.V
  have hadd_eq : addNext = add0 ∪ add1 := by
    ext e
    simp only [addNext, add0, add1, Si, rebuildPrefixS, hHE_succ, Finset.mem_union,
      Finset.mem_filter, Finset.mem_inter]
    tauto
  refine ⟨rfl, ?_, fun e _ => ?_⟩
  · change ((v.S.E \ slotsGE SP S6 slots) ∪ add0) ∪ add1 = (v.S.E \ slotsGE SP S6 slots) ∪ addNext
    rw [hadd_eq, Finset.union_assoc]
  · change (if e ∈ add1 then (coreGraph v.G v.lsf).tail e
        else if e ∈ add0 then (coreGraph v.G v.lsf).tail e else v.S.tail e) =
        (if e ∈ addNext then (coreGraph v.G v.lsf).tail e else v.S.tail e) ∧
      (if e ∈ add1 then (coreGraph v.G v.lsf).head e
        else if e ∈ add0 then (coreGraph v.G v.lsf).head e else v.S.head e) =
        (if e ∈ addNext then (coreGraph v.G v.lsf).head e else v.S.head e)
    rw [hadd_eq]
    by_cases h1 : e ∈ add1 <;> by_cases h0 : e ∈ add0 <;> simp [h1, h0]

private theorem sum_take_HE_le {SP : DSParams} {cap : ℕ} (S6 : BucketSpannerState cap)
    (slots : List ℕ) (i : ℕ) :
    ((slots.take i).map fun s => (slotHE SP S6 s).card).sum ≤
      (slots.map fun s => (slotHE SP S6 s).card).sum := by
  have h := List.take_append_drop i slots
  conv_rhs => rw [← h, List.map_append, List.sum_append]
  omega

private theorem sum_GE_add_HE_eq {SP : DSParams} {cap : ℕ} (S6 : BucketSpannerState cap)
    (slots : List ℕ) :
    (slots.map fun s => (slotGE SP S6 s).card).sum +
      (slots.map fun s => (slotHE SP S6 s).card).sum = rebuildSize SP S6 slots := by
  unfold rebuildSize
  induction slots with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons]; omega

/-! ## Core run lemma of `readRestartStmt` -/

/-- **Core run lemma of `readRestartStmt`**: independent of the outer `DSRep`, depending only on
the pointers `r + 5 ↦ sPtr`, `r + 6 ↦ gPtr`, the `S` and `G` graph blocks, the bucket spanners
`S6`, and P4's root query `Q`. Leaves `DynGraphAt st'.mem sPtr vCap eCap (v.rebuild SP S6 slots).S`,
writes below `h` only to `S`'s block and `Q.R.foot`, allocates at most `n + 2 * rebuildSize` words,
and costs (with `Q.R.phi`) at most `(800 + 2 * Q.cost) * (rebuildSize + n + 1)`. -/
theorem readRestart_core_runs {w vCap eCap cap : ℕ} {SP : DSParams} {p : Program}
    {bOps bEdge bLoop fRoot bSelf : ℕ} {Q : RootQueryAt w p fRoot}
    (hpOps : p.HasAt bOps dgOpsProcs) (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpLoop : p.HasAt bLoop (readLoopProcs bEdge))
    (hpSelf : p.HasAt bSelf (readRestartProcs bOps bEdge bLoop fRoot bSelf))
    {r sPtr gPtr spanTbl slotsPtr b4 j h : ℕ} {slots : List ℕ} {v : ReadView}
    {S6 : BucketSpannerState cap} {x6 : (bucketSpannerRep SP cap).τ}
    {s4 : Q.σ} {x4 : Q.R.τ} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (hSPe : SP.eCap ≤ eCap)
    (hrW : r + 6 < h) (_hspanW : spanTbl < 2 ^ w) (hnW : slots.length < 2 ^ w)
    (hslotsW : slotsPtr < 2 ^ w) (hb4W : b4 < 2 ^ w) (hjW : j < 2 ^ w)
    (hlist : ListAt mem slotsPtr slots) (hlist_h : slotsPtr + slots.length ≤ h)
    (hact : ∀ s ∈ slots, ∃ hs : s < cap, (S6 ⟨s, hs⟩).isSome)
    (hm5 : mem (r + 5) = sPtr) (hm6 : mem (r + 6) = gPtr)
    (hS : DynGraphAt mem sPtr vCap eCap v.S) (hG : DynGraphAt mem gPtr vCap eCap v.G)
    (hsPtrB : sPtr + dynGraphSize vCap eCap ≤ h) (hgPtrB : gPtr + dynGraphSize vCap eCap ≤ h)
    (hdisj_SG : ∀ a, sPtr ≤ a → a < sPtr + dynGraphSize vCap eCap →
      a < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ a)
    (hrep6 : (bucketSpannerRep SP cap).rep spanTbl S6 x6 mem)
    (hrep4 : Q.R.rep b4 s4 x4 mem)
    (hQok : ∀ u ∈ v.G.V, Q.ok s4 j u ∧ Q.root s4 j u = v.lsf.F.root u)
    (hfoot6 : ∀ a, (bucketSpannerRep SP cap).foot spanTbl x6 a → a < h)
    (hfoot4 : ∀ a, Q.R.foot b4 x4 a → a < h)
    (hdisj_S6 : ∀ a, sPtr ≤ a → a < sPtr + dynGraphSize vCap eCap →
      ¬ (bucketSpannerRep SP cap).foot spanTbl x6 a)
    (hdisj_S4 : ∀ a, sPtr ≤ a → a < sPtr + dynGraphSize vCap eCap → ¬ Q.R.foot b4 x4 a)
    (hdisj_G4 : ∀ a, gPtr ≤ a → a < gPtr + dynGraphSize vCap eCap → ¬ Q.R.foot b4 x4 a)
    (hdisj_64 : ∀ a, (bucketSpannerRep SP cap).foot spanTbl x6 a → ¬ Q.R.foot b4 x4 a)
    (hz : ZeroFrom mem h)
    (hroom : h + slots.length + 2 * rebuildSize SP S6 slots + 2 < 2 ^ w) :
    ∃ o st' c x4',
      Runs w p ω (readRestartStmt (bSelf + readRestartIdxCopy) (bSelf + readRestartIdxDel)
          (bSelf + readRestartIdxAdd))
        (startState [r, spanTbl, slots.length, slotsPtr, b4, j, h] mem pos) o st' c ∧
      DynGraphAt st'.mem sPtr vCap eCap (v.rebuild SP S6 slots).S ∧
      Q.R.rep b4 s4 x4' st'.mem ∧
      h ≤ o.value ∧ o.value ≤ h + slots.length + 2 * rebuildSize SP S6 slots ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, (a < sPtr ∨ sPtr + dynGraphSize vCap eCap ≤ a) →
        ¬ Q.R.foot b4 x4 a → st'.mem a = mem a) ∧
      (∀ a, Q.R.foot b4 x4' a → Q.R.foot b4 x4 a ∨ (h ≤ a ∧ a < o.value)) ∧
      c + Q.R.phi b4 x4' st'.mem ≤
        (800 + 2 * Q.cost) * (rebuildSize SP S6 slots + slots.length + 1) + Q.R.phi b4 x4 mem := by
  have hhW : h < 2 ^ w := by omega
  have hCopyProc : p.procs[bSelf + readRestartIdxCopy]? = some copyListStmt :=
    hpSelf.get (i := readRestartIdxCopy) (by simp [readRestartProcs, readRestartIdxCopy])
  have hDelProc : p.procs[bSelf + readRestartIdxDel]? = some (restartDelSlotsStmt bLoop) :=
    hpSelf.get (i := readRestartIdxDel) (by simp [readRestartProcs, readRestartIdxDel])
  have hAddProc : p.procs[bSelf + readRestartIdxAdd]? = some (restartAddSlotEdgesStmt bOps bEdge fRoot) :=
    hpSelf.get (i := readRestartIdxAdd) (by simp [readRestartProcs, readRestartIdxAdd])
  have hHE_sub_GE := slotsHE_subset_slotsGE hrep6 hact
  have hGE_HE_sum := sum_GE_add_HE_eq (SP := SP) S6 slots
  -- Step 1: Load `sPtr` and `gPtr`
  let st0 := startState [r, spanTbl, slots.length, slotsPtr, b4, j, h] mem pos
  have hr7 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 0) (.const 5)))) st0 .normal
      { st0 with regs := Function.update st0.regs 7 sPtr } 5 :=
    runs_assign_iff.mpr ⟨sPtr, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st0, startState])) (Expr.eval_const (by omega)) (by omega))
      hm5, rfl, rfl, by simp [Expr.size]⟩
  set st1 := { st0 with regs := Function.update st0.regs 7 sPtr }
  have hr8 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 0) (.const 6)))) st1 .normal
      { st1 with regs := Function.update st1.regs 8 gPtr } 5 :=
    runs_assign_iff.mpr ⟨gPtr, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st1, st0, startState])) (Expr.eval_const (by omega)) (by omega))
      hm6, rfl, rfl, by simp [Expr.size]⟩
  set st2 := { st1 with regs := Function.update st1.regs 8 gPtr }
  -- Step 2: Copy `slots` from `slotsPtr` to `[h, h + n)`
  have hCopy := runs_call_of_meetsContract (r := 9) (copyList_meetsContract hCopyProc (L := slots))
    (show evalArgs w st2 [.reg 6, .reg 3, .reg 2] = some [h, slotsPtr, slots.length] by
      simp [evalArgs, Expr.eval, st2, st1, st0, startState])
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro z (rfl | rfl | rfl) <;> omega)
    ⟨h, slotsPtr, rfl, hw16, by omega, by omega, hlist, fun i hi => Or.inl (by omega)⟩ ω
  obtain ⟨st3, c3, _, hr3, ⟨_, _, hEq3, _, hlist_copy, hfr3⟩, _, hregs3, hc3⟩ := hCopy
  simp only [List.cons.injEq, and_true] at hEq3
  obtain ⟨rfl, rfl⟩ := hEq3
  -- Step 3: `reg 10 := h + slots.length`
  have hr10 : Runs w p ω (.assign 10 (.bin .add (.reg 6) (.reg 2))) st3 .normal
      { st3 with regs := Function.update st3.regs 10 (h + slots.length) } 4 :=
    runs_assign_iff.mpr ⟨h + slots.length, Expr.eval_add
      (Expr.eval_reg_of_eq ((hregs3 6 (by decide)).trans (by simp [st2, st1, st0, startState])))
      (Expr.eval_reg_of_eq ((hregs3 2 (by decide)).trans (by simp [st2, st1, st0, startState])))
      (by omega), rfl, rfl, by simp [Expr.size]⟩
  set st4 := { st3 with regs := Function.update st3.regs 10 (h + slots.length) }
  -- Memory below `h` is untouched by `copyList`
  have hbelow3 : ∀ a < h, st3.mem a = mem a := fun a ha => hfr3 a (Or.inl ha)
  have hS3 : DynGraphAt st3.mem sPtr vCap eCap v.S :=
    hS.of_agree fun a _ ha2 => hbelow3 a (lt_of_lt_of_le ha2 hsPtrB)
  have hrep6_3 : (bucketSpannerRep SP cap).rep spanTbl S6 x6 st3.mem :=
    (bucketSpannerRep_local SP cap spanTbl S6 x6 mem st3.mem
      fun a ha => (hbelow3 a (hfoot6 a ha)).symm).1 hrep6
  -- Step 4: Call `restartDelSlotsStmt` on `[sPtr, spanTbl, h, slots.length]`
  obtain ⟨oDel, stDel, cDel, hrDel_body, ⟨hoDel, hS_del, hfrDel⟩, hcDel⟩ :=
    restartDelSlots_runs hpLoop hpEdge hpOps hw16 (by omega) hlist_copy (by omega) hnW hS3 hrep6_3
      hact hfoot6 hhW hdisj_S6 (fun i hi => Or.inr (by omega)) (pos := st4.pos) (ω := ω)
  have hrDel : Runs w p ω (.call 9 (bSelf + readRestartIdxDel) [.reg 7, .reg 1, .reg 6, .reg 2])
      st4 .normal { mem := stDel.mem, regs := Function.update st4.regs 9 oDel.value, pos := stDel.pos }
      (cDel + 5) := by
    refine runs_call_iff.mpr ⟨[sPtr, spanTbl, h, slots.length], _, oDel, stDel, cDel, ?_, hDelProc,
      hrDel_body, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    simp [evalArgs, Expr.eval, st4, hregs3 7 (by decide), hregs3 1 (by decide),
      hregs3 6 (by decide), hregs3 2 (by decide), st2, st1, st0, startState]
  set st5 : State := { mem := stDel.mem, regs := Function.update st4.regs 9 oDel.value, pos := stDel.pos }
  have h5_agree_mem : ∀ a < h, (a < sPtr ∨ sPtr + dynGraphSize vCap eCap ≤ a) → st5.mem a = mem a :=
    fun a ha hS_out => (hfrDel a hS_out).trans (hbelow3 a ha)
  have h5_agree_copy : ∀ i (hi : i < slots.length), st5.mem (h + i) = slots[i] := fun i hi => by
    rw [show st5.mem (h + i) = st3.mem (h + i) from hfrDel (h + i) (Or.inr (by omega))]
    exact hlist_copy i hi
  have hz5 : ZeroFrom st5.mem (h + slots.length) := fun a ha => by
    rw [show st5.mem a = st3.mem a from hfrDel a (Or.inr (by omega)), hfr3 a (Or.inr ha)]
    exact hz a (by omega)
  have hG5 : DynGraphAt st5.mem gPtr vCap eCap v.G :=
    hG.of_agree fun a ha1 ha2 => h5_agree_mem a (lt_of_lt_of_le ha2 hgPtrB)
      (by by_contra hnot; have := hdisj_SG a (by omega) (by omega); omega)
  have hrep6_5 : (bucketSpannerRep SP cap).rep spanTbl S6 x6 st5.mem :=
    (bucketSpannerRep_local SP cap spanTbl S6 x6 mem st5.mem fun a ha =>
      (h5_agree_mem a (hfoot6 a ha)
        (by by_contra hnot; exact hdisj_S6 a (by omega) (by omega) ha)).symm).1 hrep6
  obtain ⟨hrep4_5, hphi4_5⟩ := Q.R_local b4 s4 x4 mem st5.mem fun a ha =>
    (h5_agree_mem a (hfoot4 a ha)
      (by by_contra hnot; exact hdisj_S4 a (by omega) (by omega) ha)).symm
  -- Step 5: Loop over `i = 0 .. slots.length - 1` calling `restartAddSlotEdgesStmt`
  let h1 := h + slots.length
  let stepCost : ℕ → ℕ := fun i => (675 + 2 * Q.cost) * (slotHE SP S6 (slots.getD i 0)).card + 120
  let Inv : ℕ → State → Q.R.τ → Prop := fun i st x4i =>
    st.regs 1 = spanTbl ∧ st.regs 2 = slots.length ∧ st.regs 4 = b4 ∧ st.regs 5 = j ∧
    st.regs 6 = h ∧ st.regs 7 = sPtr ∧ st.regs 8 = gPtr ∧ st.regs 11 = i ∧
    h1 ≤ st.regs 10 ∧
    st.regs 10 ≤ h1 + 2 * ((slots.take i).map fun s => (slotHE SP S6 s).card).sum ∧
    ZeroFrom st.mem (st.regs 10) ∧
    DynGraphAt st.mem sPtr vCap eCap (rebuildPrefixS SP v S6 slots i) ∧
    Q.R.rep b4 s4 x4i st.mem ∧
    (∀ a, Q.R.foot b4 x4i a → Q.R.foot b4 x4 a ∨ (h1 ≤ a ∧ a < st.regs 10)) ∧
    (∀ a < h1, (a < sPtr ∨ sPtr + dynGraphSize vCap eCap ≤ a) →
      ¬ Q.R.foot b4 x4 a → st.mem a = st5.mem a)
  let addBody : Stmt :=
    .assign 12 (.load (.bin .add (.reg 6) (.reg 11))) ;;
    .assign 13 (.load (.bin .add (.reg 1) (.reg 12))) ;;
    .assign 14 (.load (.bin .add (.reg 13) (.const dsVCapOff))) ;;
    .assign 15 (.load (.bin .add (.reg 13) (.const dsECapOff))) ;;
    .assign 16 (.bin .add (.bin .add (.reg 13) (.const dsHdrSize))
      (.bin .add (.const 4)
        (.bin .add (.bin .mul (.const 7) (.reg 14)) (.bin .mul (.const 9) (.reg 15))))) ;;
    .call 10 (bSelf + readRestartIdxAdd) [.reg 7, .reg 8, .reg 16, .reg 4, .reg 5, .reg 10]
  obtain ⟨stLoop, cLoop, x4', hrLoop, hInvEnd, hcLoop⟩ :=
    forRange_phi_runs (Φ := fun x m => Q.R.phi b4 x m) (Inv := Inv) stepCost (n := slots.length)
      (by omega) (fun _ => hnW) (st₀ := st5) (x₀ := x4) (Expr.eval_const (by omega))
      (by refine ⟨by simp [st5, st4, hregs3 1 (by decide), st2, st1, st0, startState],
            by simp [st5, st4, hregs3 2 (by decide), st2, st1, st0, startState],
            by simp [st5, st4, hregs3 4 (by decide), st2, st1, st0, startState],
            by simp [st5, st4, hregs3 5 (by decide), st2, st1, st0, startState],
            by simp [st5, st4, hregs3 6 (by decide), st2, st1, st0, startState],
            by simp [st5, st4, hregs3 7 (by decide), st2, st1, st0, startState],
            by simp [st5, st4, hregs3 8 (by decide), st2, st1, st0, startState],
            by simp, by simp [st5, st4, h1], by simp [st5, st4, h1],
            by simpa [st5, st4, h1] using hz5,
            DynGraphAt.of_same hS_del (rebuildPrefixS_zero SP v S6 slots),
            hrep4_5 hrep4, fun a ha => Or.inl ha, fun _ _ _ _ => rfl⟩)
      (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.1)
      (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.1)
      (fun i hi st x4i hI => by
        obtain ⟨r1, r2, r4, r5, r6, r7, r8, r11, hlo, hhi, hzi, hSi, hr4i, hf4i, hfri⟩ := hI
        set s := slots[i] with hs_def
        have hs_mem : s ∈ slots := List.getElem_mem hi
        obtain ⟨hsc, ha⟩ := hact s hs_mem
        obtain ⟨b_s, d, _, hmem_b, _, hHE_eq, _, hmv_s, hme_s, _, hH_s, hfoot_bs, hHle⟩ :=
          bucketSpanner_slot_graphs hrep6_5 hsc ha
        have hbfix : b_s + dsFixedSize SP.L SP.vCap SP.eCap ≤ h := by
          have hpos := dsFixedSize_pos SP.L SP.vCap SP.eCap
          have := hfoot6 (b_s + dsFixedSize SP.L SP.vCap SP.eCap - 1)
            (hfoot_bs _ (by omega) (by omega))
          omega
        have hH_end : dsHPtr b_s SP.vCap SP.eCap + dynGraphSize SP.vCap SP.eCap ≤ h := le_trans hHle hbfix
        have hmem_foot6 : ∀ a, (bucketSpannerRep SP cap).foot spanTbl x6 a → st.mem a = st5.mem a :=
          fun a ha6 => hfri a (by have := hfoot6 a ha6; omega)
            (by by_contra hnot; exact hdisj_S6 a (by omega) (by omega) ha6) (hdisj_64 a ha6)
        have hs_val : st.mem (h + i) = s := by
          rw [hfri (h + i) (by omega) (Or.inr (by omega))
            (fun hc => by have := hfoot4 (h + i) hc; omega)]
          exact h5_agree_copy i hi
        have hbs_val : st.mem (spanTbl + s) = b_s := by
          rw [hmem_foot6 _ (Or.inl ⟨by omega, by omega⟩)]; exact hmem_b
        have hspan_s_lt : spanTbl + s < 2 ^ w :=
          lt_trans (hfoot6 _ (Or.inl ⟨by omega, by omega⟩)) hhW
        have hmv_cur : st.mem (b_s + dsVCapOff) = SP.vCap := by
          rw [hmem_foot6 _ (hfoot_bs _ (by dsimp [dsVCapOff]; omega)
            (by have := dsFixedSize_pos SP.L SP.vCap SP.eCap; dsimp [dsVCapOff]; omega))]
          exact hmv_s
        have hme_cur : st.mem (b_s + dsECapOff) = SP.eCap := by
          rw [hmem_foot6 _ (hfoot_bs _ (by dsimp [dsECapOff]; omega)
            (by have := dsFixedSize_pos SP.L SP.vCap SP.eCap; dsimp [dsECapOff]; omega))]
          exact hme_s
        have hG_cur : DynGraphAt st.mem gPtr vCap eCap v.G :=
          hG5.of_agree fun a ha1 ha2 => hfri a (by omega)
            (by by_contra hnot; have := hdisj_SG a (by omega) (by omega); omega) (hdisj_G4 a ha1 ha2)
        have hH_cur : DynGraphAt st.mem (dsHPtr b_s SP.vCap SP.eCap) SP.vCap SP.eCap (d.state SP).H :=
          hH_s.of_agree fun a ha1 ha2 => hmem_foot6 a
            (hfoot_bs a (by dsimp [dsHPtr, dsGPtr] at ha1; omega) (by omega))
        have hSagree : ∀ e ∈ (d.state SP).H.E, e ∈ (rebuildPrefixS SP v S6 slots i).E →
            (rebuildPrefixS SP v S6 slots i).tail e = (coreGraph v.G v.lsf).tail e ∧
            (rebuildPrefixS SP v S6 slots i).head e = (coreGraph v.G v.lsf).head e := by
          intro e heH heSi
          have heGE : e ∈ slotsGE SP S6 slots :=
            hHE_sub_GE (Finset.mem_biUnion.mpr ⟨s, List.mem_toFinset.mpr hs_mem, hHE_eq ▸ heH⟩)
          have hnot_base : e ∉ v.S.E \ slotsGE SP S6 slots := fun hc => (Finset.mem_sdiff.mp hc).2 heGE
          have hadd : e ∈ (slotsHE SP S6 (slots.take i) ∩ v.G.E).filter (fun e =>
              (coreGraph v.G v.lsf).tail e ∈ v.S.V ∧ (coreGraph v.G v.lsf).head e ∈ v.S.V) :=
            (Finset.mem_union.mp heSi).resolve_left hnot_base
          simp only [rebuildPrefixS, hadd, ↓reduceIte, and_self]
        -- Room for `restartAddSlotEdges_runs`
        have hHE_sum_next : ((slots.take (i + 1)).map fun s => (slotHE SP S6 s).card).sum =
            ((slots.take i).map fun s => (slotHE SP S6 s).card).sum + (d.state SP).H.m := by
          rw [List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append]
          simp [← hs_def, hHE_eq, MGraph.m]
        have hHE_sum_le : ((slots.take (i + 1)).map fun s => (slotHE SP S6 s).card).sum ≤
            rebuildSize SP S6 slots := by
          have := sum_take_HE_le (SP := SP) S6 slots (i + 1); omega
        have hroom_i : st.regs 10 + 2 * (d.state SP).H.m + 2 < 2 ^ w := by omega
        -- Execute the 5 setup assigns
        have ha12 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 6) (.reg 11)))) st .normal
            { st with regs := Function.update st.regs 12 s } 5 :=
          runs_assign_iff.mpr ⟨s, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r6)
            (Expr.eval_reg_of_eq r11) (by omega)) hs_val, rfl, rfl, by simp [Expr.size]⟩
        set stA := { st with regs := Function.update st.regs 12 s }
        have ha13 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 1) (.reg 12)))) stA .normal
            { stA with regs := Function.update stA.regs 13 b_s } 5 :=
          runs_assign_iff.mpr ⟨b_s, Expr.eval_load_of_eq (Expr.eval_add
            (Expr.eval_reg_of_eq (by simp [stA, r1])) (Expr.eval_reg_of_eq (by simp [stA]))
            hspan_s_lt) hbs_val, rfl, rfl, by simp [Expr.size]⟩
        set stB := { stA with regs := Function.update stA.regs 13 b_s }
        have ha14 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 13) (.const dsVCapOff)))) stB .normal
            { stB with regs := Function.update stB.regs 14 SP.vCap } 5 :=
          runs_assign_iff.mpr ⟨SP.vCap, Expr.eval_load_of_eq (Expr.eval_add
            (Expr.eval_reg_of_eq (by simp [stB])) (Expr.eval_const (by dsimp [dsVCapOff]; omega))
            (by have := dsFixedSize_pos SP.L SP.vCap SP.eCap; dsimp [dsVCapOff]; omega))
            hmv_cur, rfl, rfl, by simp [Expr.size]⟩
        set stC := { stB with regs := Function.update stB.regs 14 SP.vCap }
        have ha15 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 13) (.const dsECapOff)))) stC .normal
            { stC with regs := Function.update stC.regs 15 SP.eCap } 5 :=
          runs_assign_iff.mpr ⟨SP.eCap, Expr.eval_load_of_eq (Expr.eval_add
            (Expr.eval_reg_of_eq (by simp [stC, stB])) (Expr.eval_const (by dsimp [dsECapOff]; omega))
            (by have := dsFixedSize_pos SP.L SP.vCap SP.eCap; dsimp [dsECapOff]; omega))
            hme_cur, rfl, rfl, by simp [Expr.size]⟩
        set stD := { stC with regs := Function.update stC.regs 15 SP.eCap }
        have hdg_sp : 4 + (7 * SP.vCap + 9 * SP.eCap) = dynGraphSize SP.vCap SP.eCap := by
          dsimp [dynGraphSize]; omega
        have ha16 : Runs w p ω (.assign 16 (.bin .add (.bin .add (.reg 13) (.const dsHdrSize))
            (.bin .add (.const 4)
              (.bin .add (.bin .mul (.const 7) (.reg 14)) (.bin .mul (.const 9) (.reg 15))))))
            stD .normal { stD with regs := Function.update stD.regs 16 (dsHPtr b_s SP.vCap SP.eCap) } 14 :=
          runs_assign_iff.mpr ⟨dsHPtr b_s SP.vCap SP.eCap, by
            change _ = some ((b_s + dsHdrSize) + dynGraphSize SP.vCap SP.eCap)
            rw [← hdg_sp]
            have hHlt : b_s + dsHdrSize + (4 + (7 * SP.vCap + 9 * SP.eCap)) < 2 ^ w := by
              dsimp [dsHPtr, dsGPtr, dynGraphSize] at hH_end; omega
            exact Expr.eval_add
              (Expr.eval_add (Expr.eval_reg_of_eq (by simp [stD, stC, stB]))
                (Expr.eval_const (by dsimp [dsHdrSize]; omega)) (by omega))
              (Expr.eval_add (Expr.eval_const (by omega))
                (Expr.eval_add
                  (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [stD, stC])) (by omega))
                  (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [stD])) (by omega))
                  (by omega))
                (by omega))
              hHlt,
            rfl, rfl, by simp [Expr.size]⟩
        set stE := { stD with regs := Function.update stD.regs 16 (dsHPtr b_s SP.vCap SP.eCap) }
        -- Call `restartAddSlotEdgesStmt`
        have hfoot4_i : ∀ a, Q.R.foot b4 x4i a → a < st.regs 10 := fun a ha => by
          rcases hf4i a ha with h1' | h2'
          · exact lt_of_lt_of_le (lt_of_lt_of_le (hfoot4 a h1') (by omega)) hlo
          · exact h2'.2
        have hdisj_S4i : ∀ a, sPtr ≤ a → a < sPtr + dynGraphSize vCap eCap → ¬ Q.R.foot b4 x4i a :=
          fun a ha1 ha2 hc => (hf4i a hc).elim (hdisj_S4 a ha1 ha2) (by omega)
        have hdisj_G4i : ∀ a, gPtr ≤ a → a < gPtr + dynGraphSize vCap eCap → ¬ Q.R.foot b4 x4i a :=
          fun a ha1 ha2 hc => (hf4i a hc).elim (hdisj_G4 a ha1 ha2) (by omega)
        have hdisj_H4i : ∀ a, dsHPtr b_s SP.vCap SP.eCap ≤ a →
            a < dsHPtr b_s SP.vCap SP.eCap + dynGraphSize SP.vCap SP.eCap → ¬ Q.R.foot b4 x4i a :=
          fun a ha1 ha2 hc => (hf4i a hc).elim
            (hdisj_64 a (hfoot_bs a (by dsimp [dsHPtr, dsGPtr] at ha1; omega) (by omega))) (by omega)
        have hdisj_SH : ∀ a, sPtr ≤ a → a < sPtr + dynGraphSize vCap eCap →
            a < dsHPtr b_s SP.vCap SP.eCap ∨
            dsHPtr b_s SP.vCap SP.eCap + dynGraphSize SP.vCap SP.eCap ≤ a := fun a ha1 ha2 => by
          by_contra hnot
          exact hdisj_S6 a ha1 ha2 (hfoot_bs a (by dsimp [dsHPtr, dsGPtr] at *; omega) (by omega))
        obtain ⟨oAdd, stAdd, cAdd, x4_next, hrAdd_body, hAdd_lo, hAdd_hi, hzAdd, hSAdd, hr4Add,
            hf4Add, hfrAdd, hcAdd⟩ :=
          restartAddSlotEdges_runs hpOps hpEdge hw16 hSPe (by omega) (by omega) (by omega) hb4W hjW
            hSi hG_cur hH_cur hSagree hr4i hQok hfoot4_i hdisj_SG hdisj_SH hdisj_S4i hdisj_G4i
            hdisj_H4i hzi hroom_i (pos := stE.pos) (ω := ω)
        have hcallAdd : Runs w p ω (.call 10 (bSelf + readRestartIdxAdd)
            [.reg 7, .reg 8, .reg 16, .reg 4, .reg 5, .reg 10]) stE .normal
            { mem := stAdd.mem, regs := Function.update stE.regs 10 oAdd.value, pos := stAdd.pos }
            (cAdd + 7) := by
          refine runs_call_iff.mpr ⟨[sPtr, gPtr, dsHPtr b_s SP.vCap SP.eCap, b4, j, st.regs 10], _,
            oAdd, stAdd, cAdd, ?_, hAddProc, hrAdd_body, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
          simp [evalArgs, Expr.eval, stE, stD, stC, stB, stA, r4, r5, r7, r8]
        set stF : State := { mem := stAdd.mem, regs := Function.update stE.regs 10 oAdd.value, pos := stAdd.pos }
        have hb5 := runs_seq_iff.mpr (Or.inr ⟨stE, 14, cAdd + 7, ha16, hcallAdd, rfl⟩)
        have hb4 := runs_seq_iff.mpr (Or.inr ⟨stD, 5, _, ha15, hb5, rfl⟩)
        have hb3 := runs_seq_iff.mpr (Or.inr ⟨stC, 5, _, ha14, hb4, rfl⟩)
        have hb2 := runs_seq_iff.mpr (Or.inr ⟨stB, 5, _, ha13, hb3, rfl⟩)
        have hb1 := runs_seq_iff.mpr (Or.inr ⟨stA, 5, _, ha12, hb2, rfl⟩)
        refine ⟨stF, _, x4_next, hb1, by simp [stF, stE, stD, stC, stB, stA, r11], ?_, ?_⟩
        · refine ⟨by simp [stF, stE, stD, stC, stB, stA, r1], by simp [stF, stE, stD, stC, stB, stA, r2],
            by simp [stF, stE, stD, stC, stB, stA, r4], by simp [stF, stE, stD, stC, stB, stA, r5],
            by simp [stF, stE, stD, stC, stB, stA, r6], by simp [stF, stE, stD, stC, stB, stA, r7],
            by simp [stF, stE, stD, stC, stB, stA, r8], by simp, by simp [stF]; omega,
            by simp only [stF, Function.update_of_ne (by decide : (10 : ℕ) ≠ 11), Function.update_self]; rw [hHE_sum_next]; omega,
            by simpa [stF] using hzAdd, ?_, hr4Add, ?_, ?_⟩
          · have hstepS := rebuildPrefixS_step (SP := SP) (v := v) (S6 := S6) hi
            rw [← hs_def, hHE_eq] at hstepS
            exact DynGraphAt.of_same hSAdd hstepS
          · intro a ha
            simp only [stF, Function.update_of_ne (by decide : (10 : ℕ) ≠ 11), Function.update_self]
            rcases hf4Add a ha with h1' | h2'
            · rcases hf4i a h1' with h3' | h4'
              · exact Or.inl h3'
              · exact Or.inr ⟨h4'.1, lt_of_lt_of_le h4'.2 hAdd_lo⟩
            · exact Or.inr ⟨le_trans hlo h2'.1, h2'.2⟩
          · intro a ha hS_out h4_out
            have hna4i : ¬ Q.R.foot b4 x4i a := fun hc => (hf4i a hc).elim h4_out (by omega)
            exact (hfrAdd a (lt_of_lt_of_le ha hlo) hS_out hna4i).trans (hfri a ha hS_out h4_out)
        · dsimp only [stepCost]
          rw [List.getD_eq_getElem _ _ hi, ← hs_def, hHE_eq]
          change _ + Q.R.phi b4 x4_next stAdd.mem ≤ (675 + 2 * Q.cost) * (d.state SP).H.m + 120 + Q.R.phi b4 x4i st.mem
          omega)
  -- Step 6: Return `reg 10`
  have hrRet : Runs w p ω (.ret (.reg 10)) stLoop (.returned (stLoop.regs 10)) stLoop 2 :=
    runs_ret_iff.mpr ⟨stLoop.regs 10, Expr.eval_reg_of_eq rfl, rfl, rfl, by simp [Expr.size]⟩
  have hLRet := runs_seq_iff.mpr (Or.inr ⟨stLoop, cLoop, 2, hrLoop, hrRet, rfl⟩)
  have hSeq4 := runs_seq_iff.mpr (Or.inr ⟨st5, cDel + 5, _, hrDel, hLRet, rfl⟩)
  have hSeq3 := runs_seq_iff.mpr (Or.inr ⟨st4, 4, _, hr10, hSeq4, rfl⟩)
  have hSeq2 := runs_seq_iff.mpr (Or.inr ⟨st3, c3, _, hr3, hSeq3, rfl⟩)
  have hSeq1 := runs_seq_iff.mpr (Or.inr ⟨st2, 5, _, hr8, hSeq2, rfl⟩)
  have hSeq0 := runs_seq_iff.mpr (Or.inr ⟨st1, 5, _, hr7, hSeq1, rfl⟩)
  obtain ⟨_, _, _, _, _, _, _, _, hloE, hhiE, hzE, hSE, hr4E, hf4E, hfrE⟩ := hInvEnd
  have hSE' : DynGraphAt stLoop.mem sPtr vCap eCap (v.rebuild SP S6 slots).S :=
    DynGraphAt.of_same hSE (rebuildPrefixS_end hHE_sub_GE)
  have hhi_bound : stLoop.regs 10 ≤ h + slots.length + 2 * rebuildSize SP S6 slots := by
    rw [List.take_of_length_le le_rfl] at hhiE; omega
  have hsum_step : rangeCost stepCost 0 slots.length =
      (675 + 2 * Q.cost) * (slots.map fun s => (slotHE SP S6 s).card).sum + 120 * slots.length := by
    have h1 := rangeCost_eq_sum_map slots 0 (fun s => (675 + 2 * Q.cost) * (slotHE SP S6 s).card + 120)
    dsimp only [stepCost]; rw [h1]
    have hlin : ∀ (L : List ℕ) (f : ℕ → ℕ) (a b : ℕ),
        (L.map fun s => a * f s + b).sum = a * (L.map f).sum + b * L.length := by
      intro L f a b
      induction L with
      | nil => simp
      | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring
    exact hlin slots (fun s => (slotHE SP S6 s).card) (675 + 2 * Q.cost) 120
  refine ⟨.returned (stLoop.regs 10), stLoop, _, x4', hSeq0, hSE', hr4E, by simp [Outcome.value]; omega,
    by simpa [Outcome.value] using hhi_bound, hzE,
    fun a ha hS_out h4_out => (hfrE a (by omega) hS_out h4_out).trans (h5_agree_mem a ha hS_out),
    fun a ha => (hf4E a ha).imp id (fun h' => ⟨by omega, h'.2⟩), ?_⟩
  dsimp only [copyListContract, argsSize, Expr.size] at hc3 hcLoop
  rw [hsum_step, ← hphi4_5] at hcLoop
  -- Combine `490 * sumGE + (675 + 2 * Q.cost) * sumHE + ... ≤ (800 + 2 * Q.cost) * (rebuildSize + n + 1)`
  have hGE_le : 490 * (slots.map fun s => (slotGE SP S6 s).card).sum +
      (675 + 2 * Q.cost) * (slots.map fun s => (slotHE SP S6 s).card).sum ≤
      (675 + 2 * Q.cost) * rebuildSize SP S6 slots := by
    rw [← hGE_HE_sum, Nat.mul_add]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _
  have hmul_expand : (800 + 2 * Q.cost) * (rebuildSize SP S6 slots + slots.length + 1) =
      (800 + 2 * Q.cost) * rebuildSize SP S6 slots + (800 + 2 * Q.cost) * slots.length +
        (800 + 2 * Q.cost) := by ring
  have h1_le : (675 + 2 * Q.cost) * rebuildSize SP S6 slots ≤
      (800 + 2 * Q.cost) * rebuildSize SP S6 slots := Nat.mul_le_mul_right _ (by omega)
  have h2_le : 245 * slots.length ≤ (800 + 2 * Q.cost) * slots.length :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-! ## Representation wrapper (matching `ReadRep.lean`) and `ReadBranchAt.restart` -/

/-- Replacing only `S` in a `ReadRecAt` record while keeping all other cells of the record
unchanged preserves `ReadRecAt` for `{ v with S := S' }`. -/
theorem ReadRecAt.with_S {mem mem' : ℕ → ℕ} {r vCap eCap tCap L_w P : ℕ} {v : ReadView}
    {q : ReadPtrs} {S' : MGraph}
    (hrec : ReadRecAt mem r vCap eCap tCap L_w P v q)
    (hS' : DynGraphAt mem' q.s vCap eCap S')
    (hdom : ∀ e ∈ v.G.E, e < eCap)
    (hdisj : (∀ i < readRecWords, r + i < q.s ∨ q.s + dynGraphSize vCap eCap ≤ r + i) ∧
      (∀ a, q.t ≤ a → a < q.t + dynGraphSize vCap tCap → a < q.s ∨ q.s + dynGraphSize vCap eCap ≤ a) ∧
      (∀ a, q.f ≤ a → a < q.f + dynGraphSize vCap tCap → a < q.s ∨ q.s + dynGraphSize vCap eCap ≤ a) ∧
      (∀ a, q.roots ≤ a → a < q.roots + vCap → a < q.s ∨ q.s + dynGraphSize vCap eCap ≤ a) ∧
      (∀ a, q.g ≤ a → a < q.g + dynGraphSize vCap eCap → a < q.s ∨ q.s + dynGraphSize vCap eCap ≤ a) ∧
      (∀ a, q.num ≤ a → a < q.num + eCap * L_w → a < q.s ∨ q.s + dynGraphSize vCap eCap ≤ a) ∧
      (∀ a, q.den ≤ a → a < q.den + eCap * L_w → a < q.s ∨ q.s + dynGraphSize vCap eCap ≤ a))
    (hagree : ∀ a, ReadRecFoot r vCap eCap tCap L_w q a →
      (a < q.s ∨ q.s + dynGraphSize vCap eCap ≤ a) → mem' a = mem a) :
    ReadRecAt mem' r vCap eCap tCap L_w P { v with S := S' } q := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hT, hF, hR, hSt, hPr, _, hG⟩ := hrec
  obtain ⟨hdRec, hdT, hdF, hdR, hdG, hdNum, hdDen⟩ := hdisj
  have hw (i : ℕ) (hi : i < readRecWords) : mem' (r + i) = mem (r + i) :=
    hagree (r + i) (Or.inl ⟨by omega, by omega⟩) (hdRec i hi)
  have hnum (e : ℕ) (he : e ∈ v.G.E) (i : ℕ) (hi : i < L_w) :
      mem' (q.num + e * L_w + i) = mem (q.num + e * L_w + i) := by
    have heC := hdom e he
    have hlt : (e + 1) * L_w ≤ eCap * L_w := Nat.mul_le_mul_right _ (by omega)
    have hlt' : e * L_w + i < eCap * L_w := by rw [Nat.add_mul, one_mul] at hlt; omega
    exact hagree _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))))
      (hdNum _ (by omega) (by omega))
  have hden (e : ℕ) (he : e ∈ v.G.E) (i : ℕ) (hi : i < L_w) :
      mem' (q.den + e * L_w + i) = mem (q.den + e * L_w + i) := by
    have heC := hdom e he
    have hlt : (e + 1) * L_w ≤ eCap * L_w := Nat.mul_le_mul_right _ (by omega)
    have hlt' : e * L_w + i < eCap * L_w := by rw [Nat.add_mul, one_mul] at hlt; omega
    exact hagree _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))))))
      (hdDen _ (by omega) (by omega))
  have hnP : mem' (r + 7) = q.num := (hw 7 (by decide)).trans h7
  have hdP : mem' (r + 7 + 1) = q.den := (hw 8 (by decide)).trans h8
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hS', ?_⟩
  · rw [show r = r + 0 from rfl, hw 0 (by decide)]; exact h0
  · rw [hw 1 (by decide)]; exact h1
  · rw [hw 2 (by decide)]; exact h2
  · rw [hw 3 (by decide)]; exact h3
  · rw [hw 4 (by decide)]; exact h4
  · rw [hw 5 (by decide)]; exact h5
  · rw [hw 6 (by decide)]; exact h6
  · exact hnP
  · exact hdP
  · exact hT.of_agree fun a ha1 ha2 =>
      hagree a (Or.inr (Or.inl ⟨ha1, ha2⟩)) (hdT a ha1 ha2)
  · exact hF.of_agree fun a ha1 ha2 =>
      hagree a (Or.inr (Or.inr (Or.inl ⟨ha1, ha2⟩))) (hdF a ha1 ha2)
  · refine ⟨hR.1, fun x hx => ?_⟩
    rw [hagree (q.roots + x) (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
      (hdR _ (by omega) (by omega))]
    exact hR.2 x hx
  · intro e he
    obtain ⟨hvN, hvD, hpos, hval⟩ := hSt e he
    rw [h7] at hvN; rw [h8] at hvD hpos; rw [h7, h8] at hval; rw [hnP, hdP]
    refine ⟨fun i hi => (hnum e he i hi).trans_lt (hvN i hi),
      fun i hi => (hden e he i hi).trans_lt (hvD i hi), ?_, ?_⟩
    · simpa only [Num.fixVal, Num.intVal_congr (hden e he)] using hpos
    · simpa only [Num.fixVal, Num.intVal_congr (hnum e he), Num.intVal_congr (hden e he)] using hval
  · intro e he
    obtain ⟨hN, hD⟩ := hPr e he
    rw [h7] at hN; rw [h8] at hD
    rw [hnP, hdP, Num.intVal_congr (hnum e he), Num.intVal_congr (hden e he)]
    exact ⟨hN, hD⟩
  · exact hG.of_agree fun a ha1 ha2 =>
      hagree a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha1, ha2⟩)))))) (hdG a ha1 ha2)

/-- `readSpace mul vCap tCap L_w (rebuildSize + n)` dominates `n + 2 * rebuildSize + 2` whenever
`3 ≤ mul` and `1 ≤ L_w`. -/
theorem readSpace_ge_restart {mul vCap tCap L_w sz n : ℕ} (hmul : 3 ≤ mul) (hL : 1 ≤ L_w) :
    n + 2 * sz + 2 ≤ readSpace mul vCap tCap L_w (sz + n) := by
  unfold readSpace
  have h1 : 6 * (sz + n + 1) ≤ mul * (vCap + tCap + (sz + n) + 1) * (L_w + 1) := by
    have ha : 3 * (sz + n + 1) ≤ mul * (vCap + tCap + (sz + n) + 1) :=
      Nat.mul_le_mul hmul (by omega)
    have hb : 2 ≤ L_w + 1 := by omega
    calc 6 * (sz + n + 1) = (3 * (sz + n + 1)) * 2 := by ring
      _ ≤ (mul * (vCap + tCap + (sz + n) + 1)) * (L_w + 1) := Nat.mul_le_mul ha hb
  omega

/-- Condition on a `DSRep ReadView` allowing `readRestartStmt` to update `S` in place: `r + 5` and
`r + 6` hold disjoint `DynGraphAt` blocks for `S` and `G` inside the footprint, and replacing `S`
in place preserves the representation without increasing footprint or potential. -/
def ReadSExtract (vCap eCap : ℕ) (R : DSRep ReadView) : Prop :=
  ∀ r v y mem, R.rep r v y mem →
    ∃ sPtr gPtr, mem (r + 5) = sPtr ∧ mem (r + 6) = gPtr ∧
      R.foot r y (r + 5) ∧ R.foot r y (r + 6) ∧
      DynGraphAt mem sPtr vCap eCap v.S ∧ DynGraphAt mem gPtr vCap eCap v.G ∧
      (∀ a, sPtr ≤ a → a < sPtr + dynGraphSize vCap eCap → R.foot r y a) ∧
      (∀ a, gPtr ≤ a → a < gPtr + dynGraphSize vCap eCap → R.foot r y a) ∧
      (∀ a, sPtr ≤ a → a < sPtr + dynGraphSize vCap eCap →
        a < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ a) ∧
      ∀ (S' : MGraph) (mem' : ℕ → ℕ),
        DynGraphAt mem' sPtr vCap eCap S' →
        (∀ a, R.foot r y a → (a < sPtr ∨ sPtr + dynGraphSize vCap eCap ≤ a) → mem' a = mem a) →
        ∃ y', R.rep r { v with S := S' } y' mem' ∧
          (∀ a, R.foot r y' a → R.foot r y a) ∧
          R.phi r y' mem' ≤ R.phi r y mem

/-- Generic proof of the `restart` clause of `ReadBranchAt` (`ReadSpec.lean`) for any
representation satisfying `ReadSExtract` (in particular `readRep` of `ReadRep.lean`). -/
theorem readRestart_branch_clause {w vCap eCap tCap L_w cap mul : ℕ}
    {SP : DSParams} {p : Program} {bOps bEdge bLoop fRoot bSelf : ℕ}
    {Q : RootQueryAt w p fRoot} {R : DSRep ReadView}
    (hpOps : p.HasAt bOps dgOpsProcs) (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpLoop : p.HasAt bLoop (readLoopProcs bEdge))
    (hpSelf : p.HasAt bSelf (readRestartProcs bOps bEdge bLoop fRoot bSelf))
    (hw16 : 16 ≤ 2 ^ w) (hSPe : SP.eCap ≤ eCap) (hmul : 800 ≤ mul) (hL : 1 ≤ L_w)
    (hExtract : ReadSExtract vCap eCap R)
    (r spanTbl slotsPtr h b4 j : ℕ) (slots : List ℕ) (v : ReadView) (y : R.τ)
    (S6 : BucketSpannerState cap) (x6 : (bucketSpannerRep SP cap).τ) (s4 : Q.σ) (x4 : Q.R.τ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (_hrW : r < 2 ^ w) (hspanW : spanTbl < 2 ^ w) (hnW : slots.length < 2 ^ w)
    (hslotsW : slotsPtr < 2 ^ w) (hb4W : b4 < 2 ^ w) (hjW : j < 2 ^ w) (_hhW : h < 2 ^ w)
    (hlist : ListAt mem slotsPtr slots) (hlist_h : slotsPtr + slots.length ≤ h)
    (hact : ∀ s ∈ slots, ∃ hs : s < cap, (S6 ⟨s, hs⟩).isSome)
    (hR : R.rep r v y mem) (hrep6 : (bucketSpannerRep SP cap).rep spanTbl S6 x6 mem)
    (hrep4 : Q.R.rep b4 s4 x4 mem)
    (hQok : ∀ u ∈ v.G.V, Q.ok s4 j u ∧ Q.root s4 j u = v.lsf.F.root u)
    (hfootR : ∀ a, R.foot r y a → a < h)
    (hfoot6 : ∀ a, (bucketSpannerRep SP cap).foot spanTbl x6 a → a < h)
    (hfoot4 : ∀ a, Q.R.foot b4 x4 a → a < h)
    (hdisj_R6 : ∀ a, R.foot r y a → ¬ (bucketSpannerRep SP cap).foot spanTbl x6 a)
    (hdisj_R4 : ∀ a, R.foot r y a → ¬ Q.R.foot b4 x4 a)
    (hdisj_64 : ∀ a, (bucketSpannerRep SP cap).foot spanTbl x6 a → ¬ Q.R.foot b4 x4 a)
    (hz : ZeroFrom mem h)
    (hroom : h + readSpace mul vCap tCap L_w (rebuildSize SP S6 slots + slots.length) < 2 ^ w) :
    ∃ body, p.procs[bSelf + readRestartIdxMain]? = some body ∧ ∃ o st' c y' x4',
      Runs w p ω body (startState [r, spanTbl, slots.length, slotsPtr, b4, j, h] mem pos)
        o st' c ∧
      R.rep r (v.rebuild SP S6 slots) y' st'.mem ∧ Q.R.rep b4 s4 x4' st'.mem ∧
      h ≤ o.value ∧
      o.value ≤ h + readSpace mul vCap tCap L_w (rebuildSize SP S6 slots + slots.length) ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, ¬ R.foot r y a → ¬ Q.R.foot b4 x4 a → st'.mem a = mem a) ∧
      (∀ a, R.foot r y' a → R.foot r y a ∨ (h ≤ a ∧ a < o.value)) ∧
      (∀ a, Q.R.foot b4 x4' a → Q.R.foot b4 x4 a ∨ (h ≤ a ∧ a < o.value)) ∧
      (∀ a, R.foot r y' a → ¬ Q.R.foot b4 x4' a) ∧
      c + R.phi r y' st'.mem + Q.R.phi b4 x4' st'.mem ≤
        (mul + 2 * Q.cost) * (rebuildSize SP S6 slots + slots.length + 1) +
          R.phi r y mem + Q.R.phi b4 x4 mem := by
  obtain ⟨sPtr, gPtr, hm5, hm6, _, hfr6, hS, hG, hfs, hfg, hdisj_SG, hUpd⟩ := hExtract r v y mem hR
  have hr6_lt : r + 6 < h := hfootR _ hfr6
  have hsPtrB : sPtr + dynGraphSize vCap eCap ≤ h := by
    have hpos : 0 < dynGraphSize vCap eCap := by dsimp [dynGraphSize]; omega
    have := hfootR (sPtr + dynGraphSize vCap eCap - 1) (hfs _ (by omega) (by omega)); omega
  have hgPtrB : gPtr + dynGraphSize vCap eCap ≤ h := by
    have hpos : 0 < dynGraphSize vCap eCap := by dsimp [dynGraphSize]; omega
    have := hfootR (gPtr + dynGraphSize vCap eCap - 1) (hfg _ (by omega) (by omega)); omega
  have hsp_le := readSpace_ge_restart (mul := mul) (vCap := vCap) (tCap := tCap) (L_w := L_w)
    (sz := rebuildSize SP S6 slots) (n := slots.length) (by omega) hL
  obtain ⟨o, st', c, x4', hr, hS', hr4', hlo, hhi, hz', hfr', hf4', hc'⟩ :=
    readRestart_core_runs hpOps hpEdge hpLoop hpSelf hw16 hSPe hr6_lt hspanW hnW hslotsW hb4W hjW
      hlist hlist_h hact hm5 hm6 hS hG hsPtrB hgPtrB hdisj_SG hrep6 hrep4 hQok hfoot6 hfoot4
      (fun a ha1 ha2 => hdisj_R6 a (hfs a ha1 ha2))
      (fun a ha1 ha2 => hdisj_R4 a (hfs a ha1 ha2))
      (fun a ha1 ha2 => hdisj_R4 a (hfg a ha1 ha2))
      hdisj_64 hz (by omega)
  obtain ⟨y', hR', hfR', hphi'⟩ := hUpd (v.rebuild SP S6 slots).S st'.mem hS'
    (fun a ha hS_out => hfr' a (hfootR a ha) hS_out (hdisj_R4 a ha))
  have hproc : p.procs[bSelf + readRestartIdxMain]? =
      some (readRestartStmt (bSelf + readRestartIdxCopy) (bSelf + readRestartIdxDel)
        (bSelf + readRestartIdxAdd)) :=
    hpSelf.get (i := readRestartIdxMain) (by simp [readRestartProcs, readRestartIdxMain])
  have hcost1 : (800 + 2 * Q.cost) * (rebuildSize SP S6 slots + slots.length + 1) ≤
      (mul + 2 * Q.cost) * (rebuildSize SP S6 slots + slots.length + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  refine ⟨_, hproc, o, st', c, y', x4', hr, hR', hr4', hlo, by omega, hz',
    fun a ha hnR hn4 => hfr' a ha (by by_contra hnot; exact hnR (hfs a (by omega) (by omega))) hn4,
    fun a ha => Or.inl (hfR' a ha), hf4', fun a ha h4 => ?_, by omega⟩
  have hy := hfR' a ha
  rcases hf4' a h4 with h4old | ⟨hge, _⟩
  · exact hdisj_R4 a hy h4old
  · have := hfootR a hy; omega

/-- Generic `ScurRebuildAt` (`RestartIface.lean`) constructor derived directly from
`readRestart_branch_clause`. -/
noncomputable def readRestart_scurRebuildAt {vCap eCap tCap L_w cap mul : ℕ}
    {SP : DSParams} {p : Program} {bOps bEdge bLoop fRoot bSelf : ℕ}
    (Q : RootQueryAt SP.w p fRoot) {R : DSRep ReadView}
    (hpOps : p.HasAt bOps dgOpsProcs) (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpLoop : p.HasAt bLoop (readLoopProcs bEdge))
    (hpSelf : p.HasAt bSelf (readRestartProcs bOps bEdge bLoop fRoot bSelf))
    (hRloc : R.Local) (hw16 : 16 ≤ 2 ^ SP.w) (hSPe : SP.eCap ≤ eCap)
    (hmul : 800 ≤ mul) (hL : 1 ≤ L_w) (hExtract : ReadSExtract vCap eCap R) :
    ScurRebuildAt SP cap p (bSelf + readRestartIdxMain) where
  α := ReadView
  rebuild v S6 slots := v.rebuild SP S6 slots
  size _ S6 slots := rebuildSize SP S6 slots
  rep := R
  mul := mul
  space x := readSpace mul vCap tCap L_w x
  rep_local := hRloc
  σ4 := Q.σ
  rep4 := Q.R
  rep4_local := Q.R_local
  rootCost := Q.cost
  rootsOK v s4 j := ∀ u ∈ v.G.V, Q.ok s4 j u ∧ Q.root s4 j u = v.lsf.F.root u
  runs := by
    intro scurH spanTbl slotsPtr h b4 j slots v y S6 x6 s4 x4 mem pos ω
      hrW hspanW hnW hslotsW hb4W hjW hhW hlist hlist_h hact hR hrep6 hrep4 hQok
      hfootR hfoot6 hfoot4 hdisj_R6 hdisj_R4 hdisj_64 _hdisj_slots hz hroom
    obtain ⟨body, hproc, o, st', c, y', x4', hr, hR', hr4', hlo, hhi, hz', hfr', hfR', hf4',
        hdisj', hc'⟩ :=
      readRestart_branch_clause hpOps hpEdge hpLoop hpSelf hw16 hSPe hmul hL hExtract
        scurH spanTbl slotsPtr h b4 j slots v y S6 x6 s4 x4 mem pos ω
        hrW hspanW hnW hslotsW hb4W hjW hhW hlist hlist_h hact hR hrep6 hrep4 hQok
        hfootR hfoot6 hfoot4 hdisj_R6 hdisj_R4 hdisj_64 hz hroom
    have hlog1 : 1 ≤ ordStoreLog SP.eCap := by unfold ordStoreLog; omega
    have hcost2 : (mul + 2 * Q.cost) * (rebuildSize SP S6 slots + slots.length + 1) ≤
        (mul + 2 * Q.cost) * (rebuildSize SP S6 slots + slots.length + 1) * ordStoreLog SP.eCap :=
      Nat.le_mul_of_pos_right _ (by omega)
    exact ⟨body, hproc, o, st', c, y', x4', hr, hR', hr4', hlo, hhi, hz', hfr', hfR', hf4',
      hdisj', by omega⟩

end MinCostFlow.SparseCore.Program.Read
