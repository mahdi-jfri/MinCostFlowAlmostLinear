module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4ScanDleft
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4ScanUH
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSlotScanR
public import MinCostFlow.SparseCore.Program.AssemblyFirstEmbCopy

import WordRAM.Tactic

/-!
# The work of Phase 4 after the spanner update of one slot (`AssemblyFirstStepP4TaskDefs`)

After the spanner of an old active slot has taken its batch, Phase 4 reads what the update put out
and records it in the Phase 4 workspace. This file gives the procedure that does this and the
pure picture of what it leaves in the workspace.

* `p4TaskScan P d OS UH D R S`: the workspace after the copy buffer is emptied and the scans of
  the spanner's batch `U_H`, of the list `D` and of the list `R`, where `d` is the new history of
  the slot and `OS` the old output graph.
* `p4TaskWS P d OS UH D R S`: the workspace after the scan of the walks of `D_left` as well.
* `asmFirstP4AfterStmt`, with arguments `[spanTbl, slot, hOut, ws, eCap, oldS, embH, h]`: it reads
  the slot's handle, finds the presence arrays of the slot's graph and spanner, empties the copy
  buffer, runs the four scans, and copies the walks of the edges of the copy buffer into the
  embedding. It returns the new heap pointer.

The pure lemmas say that every edge of the copy buffer is an edge of the slot's new graph
(`mem_p4TaskScan_copyBuf`), that emptying the copy buffer keeps the rest of the workspace
(`phase4WSAt_resetCopy`), and that a block of cells that avoids the workspace lies on one side of
it (`block_avoid`). The run lemma is in `AssemblyFirstStepP4After.lean`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Read

@[expose] public section

/-- The workspace after the copy buffer is emptied and the scans of `U_H`, `D` and `R` of an old
active slot whose new history is `d`. -/
noncomputable def p4TaskScan (P : DSParams) (d : DSHist) (OS : Finset ℕ) (UH : List Update)
    (D R : List ℕ) (S : Phase4WS) : Phase4WS :=
  R.foldl (p4StepR (d.state P).G.E (d.state P).H.E true)
    (D.foldl (p4StepD (d.state P).G.E (d.state P).H.E)
      (UH.foldl (p4StepUH (d.state P).G.E (d.state P).H.E OS true) { S with copyBuf := [] }))

/-- The workspace after the scan of the walks of `D_left` as well. -/
noncomputable def p4TaskWS (P : DSParams) (d : DSHist) (OS : Finset ℕ) (UH : List Update)
    (D R : List ℕ) (S : Phase4WS) : Phase4WS :=
  (p4TaskScan P d OS UH D R S).copyBuf.foldl
    (p4StepDleft (d.state P).G.E (d.state P).H.E OS (piTotal (d.state P)))
    (p4TaskScan P d OS UH D R S)

/-- The calls of the work after the update of one slot (see `asmFirstP4AfterStmt`). -/
def asmFirstP4AfterTail (fScanUH fScanD fScanR fDleft fCopy : ℕ) : Stmt :=
  .call 14 fScanUH [.reg 11, .reg 12, .load (.reg 2), .reg 3, .reg 4, .const 1, .reg 5] ;;
  .call 14 fScanD [.reg 11, .reg 12, .load (.bin .add (.reg 2) (.const 3)),
    .load (.bin .add (.reg 2) (.const 4)), .reg 3, .reg 4] ;;
  .call 14 fScanR [.reg 11, .reg 12, .load (.bin .add (.reg 2) (.const 5)),
    .load (.bin .add (.reg 2) (.const 6)), .const 1, .reg 3, .reg 4] ;;
  .call 14 fDleft [.reg 11, .reg 12, .reg 3, .reg 4, .reg 5, .reg 8] ;;
  .call 14 fCopy [.reg 6, .reg 0, .reg 1, .bin .add (.reg 13) (.const 1), .load (.reg 13),
    .reg 7] ;;
  .ret (.reg 14)

/-- **The work after the update of one slot**, `[spanTbl, slot, hOut, ws, eCap, oldS, embH, h]`.
Register `8` gets the handle `b` of the slot, registers `9` and `10` the sizes `vCap` and `eCap`
of its spanner, and registers `11` and `12` the places of the presence arrays of its graph and
of its spanner. Register `13` is the place of the length of the copy buffer, which is set to `0`.
Then come the scans of `U_H`, `D`, `R` (the header of the outputs is at `hOut`) and of the walks
of `D_left`, and the copy of the walks of the copy buffer into the embedding at `embH`. -/
def asmFirstP4AfterStmt (fScanUH fScanD fScanR fDleft fCopy : ℕ) : Stmt :=
  .assign 8 (.load (.bin .add (.reg 0) (.reg 1))) ;;
  .assign 9 (.load (.bin .add (.reg 8) (.const 3))) ;;
  .assign 10 (.load (.bin .add (.reg 8) (.const 4))) ;;
  .assign 11 (.bin .add (.reg 8) (.bin .add (.const 10) (.bin .mul (.const 7) (.reg 9)))) ;;
  .assign 12 (.bin .add (.reg 11) (.bin .add (.const 4)
    (.bin .add (.bin .mul (.const 7) (.reg 9)) (.bin .mul (.const 9) (.reg 10))))) ;;
  .assign 13 (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 10) (.reg 4))) (.const 3)) ;;
  .store (.reg 13) (.const 0) ;;
  asmFirstP4AfterTail fScanUH fScanD fScanR fDleft fCopy

/-- What the work after the update of slot `s` (new history `d`) leaves, from the memory `mem₀`
and the workspace `S`, with the outputs `UH`, `dL`, `rL` of the update. Let `eL` be the copy
buffer `(p4TaskScan P d OS UH dL rL S).copyBuf`. The procedure returns the heap pointer
`h + slotListWalkWords P S6 s eL`, the workspace is `p4TaskWS P d OS UH dL rL S`, the embedding
holds the new walks of the edges of `eL` in new cells between `h` and the returned pointer, the
spanners keep their representation, the memory from the returned pointer on is zero, and every
cell below `h` outside the embedding and outside the workspace is kept. -/
def P4AfterPost (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (x6 : BucketSpannerMeta P.L cap) (spanTbl s ws eCap embH h : ℕ) (d : DSHist)
    (OS : Finset ℕ) (UH : List Update) (dL rL : List ℕ) (S : Phase4WS) (v : EmbView)
    (y : EmbConc) (mem₀ : ℕ → ℕ) (o : Outcome) (st' : State) : Prop :=
  o = .returned (h + slotListWalkWords P S6 s (p4TaskScan P d OS UH dL rL S).copyBuf) ∧
  Phase4WSAt st'.mem ws eCap (p4TaskWS P d OS UH dL rL S) ∧
  (∃ y', (embRep eCap).rep embH (v.apply (slotChange P S6 s (p4TaskScan P d OS UH dL rL S).copyBuf))
      y' st'.mem ∧
    ∀ a, embFoot eCap embH y' a → embFoot eCap embH y a ∨
      (h ≤ a ∧ a < h + slotListWalkWords P S6 s (p4TaskScan P d OS UH dL rL S).copyBuf)) ∧
  (bucketSpannerRep P cap).rep spanTbl S6 x6 st'.mem ∧
  ZeroFrom st'.mem (h + slotListWalkWords P S6 s (p4TaskScan P d OS UH dL rL S).copyBuf) ∧
  ∀ a < h, ¬ embFoot eCap embH y a → (a < ws ∨ ws + p4WsSize eCap ≤ a) → st'.mem a = mem₀ a

end

/-! ## Determinism -/

public section

theorem asmFirstP4AfterStmt_noRand (fScanUH fScanD fScanR fDleft fCopy : ℕ) :
    (asmFirstP4AfterStmt fScanUH fScanD fScanR fDleft fCopy).NoRand := by
  simp [asmFirstP4AfterStmt, asmFirstP4AfterTail, Stmt.NoRand]

end

/-! ## The copy buffer holds edges of the new graph -/

public section

theorem mem_pushCopy_copyBuf {S : Phase4WS} {e x : ℕ} (h : x ∈ (pushCopy S e).copyBuf) :
    x ∈ S.copyBuf ∨ x = e := by
  unfold pushCopy at h
  split_ifs at h
  · exact Or.inl h
  · simpa using h

/-- A property of the workspace that each step keeps holds after a fold of the steps. -/
theorem foldl_keeps {α : Type} (Q : Phase4WS → Prop) (f : Phase4WS → α → Phase4WS)
    (hf : ∀ S a, Q S → Q (f S a)) (l : List α) (S : Phase4WS) (hS : Q S) : Q (l.foldl f S) := by
  induction l generalizing S with
  | nil => exact hS
  | cons a l ih => exact ih _ (hf S a hS)

theorem p4StepEdge_copyBuf_sub {GE HE : Finset ℕ} {fD fDel fIns fCopy : Bool} {S : Phase4WS}
    {e x : ℕ} (h : x ∈ (p4StepEdge GE HE fD fDel fIns fCopy S e).copyBuf) :
    x ∈ S.copyBuf ∨ (fCopy = true ∧ x = e) := by
  cases fCopy with
  | false => rw [p4StepEdge_copyBuf] at h; exact Or.inl h
  | true =>
    have hp : p4StepEdge GE HE fD fDel fIns true S e =
        pushCopy (p4StepEdge GE HE fD fDel fIns false S e) e := by
      simp only [p4StepEdge, Bool.false_eq_true, ↓reduceIte]
    rw [hp] at h
    rcases mem_pushCopy_copyBuf h with h | h
    · rw [p4StepEdge_copyBuf] at h; exact Or.inl h
    · exact Or.inr ⟨rfl, h⟩

/-- Every edge of the copy buffer after the scans of `U_H`, `D` and `R` is an edge of the slot's
new graph: the scan of `U_H` copies an edge only when it is in the graph (`p4StepUH`), the scan of
`D` copies nothing, and the scan of `R` copies an edge only when it is in the graph
(`p4StepR`). -/
theorem mem_p4TaskScan_copyBuf {P : DSParams} {d : DSHist} {OS : Finset ℕ} {UH : List Update}
    {D R : List ℕ} {S : Phase4WS} {x : ℕ} (hx : x ∈ (p4TaskScan P d OS UH D R S).copyBuf) :
    x ∈ (d.state P).G.E := by
  classical
  let Q : Phase4WS → Prop := fun T => ∀ y ∈ T.copyBuf, y ∈ (d.state P).G.E
  have hUH : ∀ T u, Q T → Q (p4StepUH (d.state P).G.E (d.state P).H.E OS true T u) := by
    intro T u hT y hy
    cases u with
    | insert e a b =>
      rcases p4StepEdge_copyBuf_sub hy with h | ⟨h, -⟩
      · exact hT y h
      · exact absurd h (by decide)
    | delete e =>
      rcases p4StepEdge_copyBuf_sub hy with h | ⟨h, rfl⟩
      · exact hT y h
      · simp only [Bool.true_and, decide_eq_true_eq] at h
        exact h.1
    | split a b c f => exact hT y hy
  have hD : ∀ T e, Q T → Q (p4StepD (d.state P).G.E (d.state P).H.E T e) := by
    intro T e hT y hy
    exact hT y (by simpa [p4StepD] using hy)
  have hR : ∀ T e, Q T → Q (p4StepR (d.state P).G.E (d.state P).H.E true T e) := by
    intro T e hT y hy
    unfold p4StepR at hy
    split_ifs at hy with hc
    · rcases mem_pushCopy_copyBuf hy with h | rfl
      · exact hT y h
      · exact hc.2.1
    · exact hT y hy
  refine foldl_keeps Q _ hR R _ (foldl_keeps Q _ hD D _ (foldl_keeps Q _ hUH UH _ ?_)) x hx
  intro y hy
  simp at hy

/-- The copy buffer has no repeated edge and its edges are below `eCap`, so it has at most
`eCap` edges. -/
theorem phase4WSAt_copyBuf_length_le {mem : ℕ → ℕ} {ws eCap : ℕ} {S : Phase4WS}
    (h : Phase4WSAt mem ws eCap S) : S.copyBuf.length ≤ eCap := by
  obtain ⟨-, -, -, -, -, -, -, hnd, hcb, -, -⟩ := h
  rw [← List.toFinset_card_of_nodup hnd]
  calc S.copyBuf.toFinset.card ≤ (Finset.range eCap).card :=
        Finset.card_le_card fun e he => Finset.mem_range.mpr (hcb e (List.mem_toFinset.mp he)).1
    _ = eCap := Finset.card_range eCap

theorem p4TaskWS_copyBuf (P : DSParams) (d : DSHist) (OS : Finset ℕ) (UH : List Update)
    (D R : List ℕ) (S : Phase4WS) :
    (p4TaskWS P d OS UH D R S).copyBuf = (p4TaskScan P d OS UH D R S).copyBuf :=
  foldl_p4StepDleft_copyBuf _ _ _ _ _ _

/-! ## Emptying the copy buffer -/

/-- Setting the length of the copy buffer to `0` empties the copy buffer and keeps the rest of
the workspace, since the length cell is apart from the other parts. -/
theorem phase4WSAt_resetCopy {mem : ℕ → ℕ} {ws eCap : ℕ} {S : Phase4WS}
    (h : Phase4WSAt mem ws eCap S) :
    Phase4WSAt (Function.update mem (p4CopyLen ws eCap) 0) ws eCap { S with copyBuf := [] } := by
  obtain ⟨hD, hA, hT, hDS, hIS, hR, hSC, -, -, -, -⟩ := h
  have hne : ∀ a, a ≠ p4CopyLen ws eCap → Function.update mem (p4CopyLen ws eCap) 0 a = mem a :=
    fun a ha => Function.update_of_ne ha _ _
  have hlenDS := dedupBuf_length_le hDS
  have hlenIS := dedupBuf_length_le hIS
  have hlenR := dedupBuf_length_le hR
  refine ⟨fun e he => (hne _ (by simp [p4InDtot, p4CopyLen]; omega)).trans (hD e he),
    fun e he => (hne _ (by simp [p4InAct, p4CopyLen]; omega)).trans (hA e he),
    fun e he => (hne _ (by simp [p4InTgt, p4CopyLen]; omega)).trans (hT e he),
    dedupBufAt_of_agree_cap hDS (fun e he => hne _ (by simp [p4InDelSup, p4CopyLen]; omega))
      (fun i hi => hne _ (by simp [p4DelSup, p4CopyLen]; omega))
      (hne _ (by simp [p4DelLen, p4CopyLen])),
    dedupBufAt_of_agree_cap hIS (fun e he => hne _ (by simp [p4InInsSup, p4CopyLen]; omega))
      (fun i hi => hne _ (by simp [p4InsSup, p4CopyLen]; omega))
      (hne _ (by simp [p4InsLen, p4CopyLen])),
    dedupBufAt_of_agree_cap hR (fun e he => hne _ (by simp [p4InReemb, p4CopyLen]; omega))
      (fun i hi => hne _ (by simp [p4Reemb, p4CopyLen]; omega))
      (hne _ (by simp [p4ReembLen, p4CopyLen])),
    fun e he => (hne _ (by simp [p4SeenCopy, p4CopyLen]; omega)).trans (hSC e he),
    List.nodup_nil, fun _ h => (by cases h), by simp, fun _ h => (by cases h)⟩

/-! ## Blocks that avoid the workspace -/

/-- If every cell of the block `[a, a + n)`, with `0 < n`, is outside `[ws, ws + k)`, with
`0 < k`, then the whole block lies before `ws` or after `ws + k`: otherwise the cell `ws` (when
`a < ws`) or the cell `a` (when `ws ≤ a`) would be inside. -/
theorem block_avoid {a n ws k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (h : ∀ i < n, a + i < ws ∨ ws + k ≤ a + i) : a + n ≤ ws ∨ ws + k ≤ a := by
  by_contra hc
  push Not at hc
  rcases lt_or_ge a ws with ha | ha
  · rcases h (ws - a) (by omega) with h' | h' <;> omega
  · rcases h 0 hn with h' | h' <;> omega

end

end MinCostFlow.SparseCore.Program
