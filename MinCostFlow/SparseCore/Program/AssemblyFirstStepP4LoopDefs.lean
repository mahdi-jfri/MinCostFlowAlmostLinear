module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4Task
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4Congr
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepOutEmbModel

import WordRAM.Tactic

/-!
# The loop over the tasks of Phase 4: the model (`AssemblyFirstStepP4LoopDefs`)

Phase 4 runs one task per old active slot whose bundle changed (`asmFirstP4TaskStmt`). The
descriptors `[slot, batchPtr, W]` of the tasks come from Phase 3 (`AsmFirstBunStepOut`). This file
gives the pure model of the loop over the tasks, so that the run lemma of the loop
(`AssemblyFirstStepP4Loop.lean`) can state what the loop leaves.

* `p4OnTask` reads a value from a task: one value when the slot holds a history and the batch is
  not empty, and a default value otherwise. A task with an empty batch does nothing.
* `p4SpanAfter`: the spanners after the tasks. Each task appends its batch to the history of its
  slot (`p4NewHist`).
* `P4TaskOut`: the outputs `U_H`, `D`, `R` of the update of a task, as lists. The loop knows them
  only up to order, through `P4OutFacts`.
* `p4WVStep`: what a task does to the workspace and to the embedding table.
* `p4TaskPay` and `p4TaskSpace`: the amortized cost and the space of a task. They depend only on
  the model, not on the order of the outputs: the copy buffer of a task holds distinct edges of
  the set `p4CopyCand` (`mem_p4TaskScan_copyBuf_cand`), so its work is at most a sum over this
  set (`p4_copy_work_le`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Read MinCostFlow.SparseCore.Program.Restart

/-! ## The model -/

@[expose] public section

/-- The outputs of the update of one task: the batch `U_H` of the spanner, and the lists of the
sets `D` and `R`. -/
structure P4TaskOut where
  UH : List Update
  dL : List ℕ
  rL : List ℕ

/-- A value read from task `t` on the spanners `S6` and the memory `mem₀`: `f` on the slot and
its history when the slot holds a history and the batch of `t` is not empty, and `dflt`
otherwise. -/
noncomputable def p4OnTask {α : Type} {cap : ℕ} (S6 : BucketSpannerState cap) (mem₀ : ℕ → ℕ)
    (dflt : α) (f : (s : ℕ) → s < cap → DSHist → α) (t : SpanUpdTask) : α :=
  if hs : t.slot < cap then
    match S6 ⟨t.slot, hs⟩ with
    | some d => if mem₀ t.batchPtr = 0 then dflt else f t.slot hs d
    | none => dflt
  else dflt

/-- The history `d` with the batch of task `t` appended. The batch is read on the graph of `d`. -/
noncomputable def p4NewHist (P : DSParams) (mem₀ : ℕ → ℕ) (d : DSHist) (t : SpanUpdTask) :
    DSHist :=
  ⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩

/-- One task on the spanners `S`: the slot of `t` gets its new history. -/
noncomputable def p4SpanStep (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) (S : BucketSpannerState cap) (t : SpanUpdTask) : BucketSpannerState cap :=
  p4OnTask S6 mem₀ S (fun s hs d => S.set ⟨s, hs⟩ (some (p4NewHist P mem₀ d t))) t

/-- The spanners after the tasks `ts`. -/
noncomputable def p4SpanAfter (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) (ts : List SpanUpdTask) : BucketSpannerState cap :=
  ts.foldl (p4SpanStep P S6 mem₀) S6

/-- The facts that the update of the history `d` with the batch `U` gives about its outputs. -/
def P4OutFacts (P : DSParams) (d : DSHist) (U : List Update) (o : P4TaskOut) : Prop :=
  o.UH.Perm (update (d.state P) U (canonicalSparsify P.impl)).UH ∧
  (d.state P).H.applyBatch o.UH = (update (d.state P) U (canonicalSparsify P.impl)).state.H ∧
  o.dL.Nodup ∧ o.dL.toFinset = (update (d.state P) U (canonicalSparsify P.impl)).D ∧
  o.rL.Nodup ∧ o.rL.toFinset = updateReembSet (d.state P) U (canonicalSparsify P.impl) ∧
  Theorem82Clauses d.G₀ P.L P.splitBound (dsSparsifyParams P) (canonicalSparsify P.impl)
    (d.Us ++ [U])

/-- The edges that the update of `d` with `U` outputs, and the edges of the walks of the new
spanner, are below `eCap`. -/
def P4TaskCaps (P : DSParams) (eCap : ℕ) (d : DSHist) (U : List Update) : Prop :=
  (∀ u ∈ (update (d.state P) U (canonicalSparsify P.impl)).UH, UpdEdgeBelow eCap u) ∧
  (∀ e ∈ (update (d.state P) U (canonicalSparsify P.impl)).D, e < eCap) ∧
  (∀ e ∈ updateReembSet (d.state P) U (canonicalSparsify P.impl), e < eCap) ∧
  (∀ e ∈ ((⟨d.G₀, d.Us ++ [U]⟩ : DSHist).state P).G.E,
    ∀ q ∈ piTotal ((⟨d.G₀, d.Us ++ [U]⟩ : DSHist).state P) e, q.1 < eCap)

/-- The outputs `q.2` of task `q.1` meet `P4OutFacts` when the task updates its slot. -/
def P4OutOK (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap) (mem₀ : ℕ → ℕ)
    (q : SpanUpdTask × P4TaskOut) : Prop :=
  ∀ (hs : q.1.slot < cap) (d : DSHist), S6 ⟨q.1.slot, hs⟩ = some d → mem₀ q.1.batchPtr ≠ 0 →
    P4OutFacts P d (decodeBatch mem₀ q.1.batchPtr (d.state P).G).1 q.2

/-- What task `q.1`, with the outputs `q.2`, does to the workspace and to the embedding table. -/
noncomputable def p4WVStep (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) (OS : Finset ℕ) (A : Phase4WS × EmbView) (q : SpanUpdTask × P4TaskOut) :
    Phase4WS × EmbView :=
  p4OnTask S6 mem₀ A (fun s hs d =>
    (p4TaskWS P (p4NewHist P mem₀ d q.1) OS q.2.UH q.2.dL q.2.rL A.1,
     A.2.apply (slotChange P (S6.set ⟨s, hs⟩ (some (p4NewHist P mem₀ d q.1))) s
       (p4TaskScan P (p4NewHist P mem₀ d q.1) OS q.2.UH q.2.dL q.2.rL A.1).copyBuf))) q.1

/-- The edges that the update of `d` with `U` may put into the copy buffer: the edges deleted
from the spanner and the edges to embed again, when they are in the new graph but not in the new
spanner. -/
noncomputable def p4CopyCand (P : DSParams) (d : DSHist) (U : List Update) : Finset ℕ :=
  ((uhDelFinset (update (d.state P) U (canonicalSparsify P.impl)).UH ∪
      updateReembSet (d.state P) U (canonicalSparsify P.impl)) ∩
    ((⟨d.G₀, d.Us ++ [U]⟩ : DSHist).state P).G.E) \
    ((⟨d.G₀, d.Us ++ [U]⟩ : DSHist).state P).H.E

/-- The steps spent on one edge of the copy buffer: the scan of its walk and the copy of its
walk into the embedding table. -/
noncomputable def p4CopyEdgeCost (P : DSParams) {cap : ℕ} (S : BucketSpannerState cap) (s : ℕ)
    (d' : DSHist) (e : ℕ) : ℕ :=
  p4DleftEdgeCost P d' e +
    142 * (Read.walkWords (slotWalk P S s e) + (if d'.Us = [] then 0 else P.L) + 2)

/-- A bound on the work after the update of `d` with `U` at slot `s`: the scans of the outputs
and the work on the copy candidates. -/
noncomputable def p4TaskWorkOf (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap) (s : ℕ)
    (hs : s < cap) (d : DSHist) (U : List Update) : ℕ :=
  340 * (update (d.state P) U (canonicalSparsify P.impl)).UH.length +
    170 * (update (d.state P) U (canonicalSparsify P.impl)).D.card +
    135 * (updateReembSet (d.state P) U (canonicalSparsify P.impl)).card +
    (p4CopyCand P d U).sum
      (p4CopyEdgeCost P (S6.set ⟨s, hs⟩ (some ⟨d.G₀, d.Us ++ [U]⟩)) s ⟨d.G₀, d.Us ++ [U]⟩)

/-- What a task may pay: the amortized cost of the update and the work after it. -/
noncomputable def p4TaskPay (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) (t : SpanUpdTask) : ℕ :=
  p4OnTask S6 mem₀ 0 (fun s hs d => dsUpdateAmortCost P d [0, t.batchPtr, t.W, 0] mem₀ +
    p4TaskWorkOf P S6 s hs d (decodeBatch mem₀ t.batchPtr (d.state P).G).1 + 600) t

/-- The space of a task: the space of the update and the words of the walks of all edges of the
new graph. -/
noncomputable def p4TaskSpace (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) (t : SpanUpdTask) : ℕ :=
  p4OnTask S6 mem₀ 0 (fun s hs d => dsUpdateOpSpace P d [0, t.batchPtr, t.W, 0] mem₀ +
    ((p4NewHist P mem₀ d t).state P).G.E.sum
      (fun e => Read.walkWords (slotWalk P (S6.set ⟨s, hs⟩ (some (p4NewHist P mem₀ d t))) s e))) t

/-- A cell that the loop keeps: it is outside the spanners, outside the embedding table and
outside the workspace. -/
def P4Free {L cap : ℕ} (spanTbl : ℕ) (x6 : BucketSpannerMeta L cap) (eCap embH : ℕ)
    (y : EmbConc) (ws a : ℕ) : Prop :=
  ¬ bucketFoot spanTbl x6 a ∧ ¬ embFoot eCap embH y a ∧ (a < ws ∨ ws + p4WsSize eCap ≤ a)

end

/-! ## Reading a task -/

public section

theorem p4OnTask_of {α : Type} {cap : ℕ} {S6 : BucketSpannerState cap} {mem₀ : ℕ → ℕ}
    {dflt : α} {f : (s : ℕ) → s < cap → DSHist → α} {t : SpanUpdTask} (hs : t.slot < cap)
    {d : DSHist} (hd : S6 ⟨t.slot, hs⟩ = some d) (hb : mem₀ t.batchPtr ≠ 0) :
    p4OnTask S6 mem₀ dflt f t = f t.slot hs d := by
  simp only [p4OnTask, hs, ↓reduceDIte, hd, hb, ↓reduceIte]

theorem p4OnTask_empty {α : Type} {cap : ℕ} {S6 : BucketSpannerState cap} {mem₀ : ℕ → ℕ}
    {dflt : α} {f : (s : ℕ) → s < cap → DSHist → α} {t : SpanUpdTask} (hs : t.slot < cap)
    {d : DSHist} (hd : S6 ⟨t.slot, hs⟩ = some d) (hb : mem₀ t.batchPtr = 0) :
    p4OnTask S6 mem₀ dflt f t = dflt := by
  simp only [p4OnTask, hs, ↓reduceDIte, hd, hb, ↓reduceIte]

/-- A task changes only the slot of its own: the other slots keep their history. -/
theorem p4SpanAfter_unchanged (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) {ts : List SpanUpdTask} {j : Fin cap} (hnot : j.1 ∉ ts.map SpanUpdTask.slot)
    (S : BucketSpannerState cap) : ts.foldl (p4SpanStep P S6 mem₀) S j = S j := by
  induction ts generalizing S with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hnot
    rw [List.foldl_cons, ih hnot.2]
    unfold p4SpanStep p4OnTask
    by_cases hs : t.slot < cap
    · simp only [hs, ↓reduceDIte]
      cases S6 ⟨t.slot, hs⟩ with
      | none => rfl
      | some d =>
        by_cases hb : mem₀ t.batchPtr = 0
        · simp only [hb, ↓reduceIte]
        · have hne : j ≠ ⟨t.slot, hs⟩ := fun h => hnot.1 (congrArg Fin.val h)
          simp [hb, BucketSpannerState.set, Function.update_of_ne hne]
    · simp only [hs, ↓reduceDIte]

/-! ## Walks of one slot -/

/-- The walk of an edge at slot `s` depends only on the history at slot `s`. -/
theorem slotWalk_set_self (P : DSParams) {cap : ℕ} (S S' : BucketSpannerState cap) {s : ℕ}
    (hs : s < cap) (x : Option DSHist) (e : ℕ) :
    slotWalk P (S.set ⟨s, hs⟩ x) s e = slotWalk P (S'.set ⟨s, hs⟩ x) s e := by
  simp [slotWalk, hs, BucketSpannerState.set]

theorem slotChange_set_self (P : DSParams) {cap : ℕ} (S S' : BucketSpannerState cap) {s : ℕ}
    (hs : s < cap) (x : Option DSHist) (es : List ℕ) :
    slotChange P (S.set ⟨s, hs⟩ x) s es = slotChange P (S'.set ⟨s, hs⟩ x) s es := by
  unfold slotChange
  exact List.map_congr_left fun e _ => by rw [slotWalk_set_self P S S' hs x e]

theorem slotListWalkWords_set_self (P : DSParams) {cap : ℕ} (S S' : BucketSpannerState cap)
    {s : ℕ} (hs : s < cap) (x : Option DSHist) (es : List ℕ) :
    slotListWalkWords P (S.set ⟨s, hs⟩ x) s es = slotListWalkWords P (S'.set ⟨s, hs⟩ x) s es := by
  unfold slotListWalkWords
  congr 1
  exact List.map_congr_left fun e _ => by rw [slotWalk_set_self P S S' hs x e]

theorem slotListCopyWork_set_self (P : DSParams) {cap : ℕ} (S S' : BucketSpannerState cap)
    {s : ℕ} (hs : s < cap) (x : Option DSHist) (d : DSHist) (es : List ℕ) :
    slotListCopyWork P (S.set ⟨s, hs⟩ x) s d es =
      slotListCopyWork P (S'.set ⟨s, hs⟩ x) s d es := by
  unfold slotListCopyWork
  congr 1
  exact List.map_congr_left fun e _ => by rw [slotWalk_set_self P S S' hs x e]

/-! ## The copy buffer of a task -/

/-- Two orders of the same batch delete the same edges. -/
theorem uhDelFinset_perm {l₁ l₂ : List Update} (h : l₁.Perm l₂) :
    uhDelFinset l₁ = uhDelFinset l₂ := by
  unfold uhDelFinset
  exact List.toFinset_eq_of_perm _ _ (h.filterMap _)

/-- A fold keeps a property when each step with an element of the list keeps it. -/
theorem foldl_keeps_mem {α : Type} (Q : Phase4WS → Prop) (f : Phase4WS → α → Phase4WS)
    (l : List α) (hf : ∀ S a, a ∈ l → Q S → Q (f S a)) (S : Phase4WS) (hS : Q S) :
    Q (l.foldl f S) := by
  induction l generalizing S with
  | nil => exact hS
  | cons a l ih =>
    exact ih (fun T b hb hT => hf T b (List.mem_cons_of_mem a hb) hT) _
      (hf S a List.mem_cons_self hS)

/-- Every edge of the copy buffer after the scans of `U_H`, `D` and `R` is deleted from the
spanner by `U_H` or is in `R`, is in the slot's new graph and is not in its new spanner. The scan
of `U_H` copies only the deleted edges that are in the graph and not in the spanner
(`p4StepUH`), the scan of `D` copies nothing, and the scan of `R` copies only edges of `R` that
are in the graph and not in the spanner (`p4StepR`). -/
theorem mem_p4TaskScan_copyBuf_cand {P : DSParams} {d : DSHist} {OS : Finset ℕ}
    {UH : List Update} {D R : List ℕ} {S : Phase4WS} {x : ℕ}
    (hx : x ∈ (p4TaskScan P d OS UH D R S).copyBuf) :
    (x ∈ uhDelFinset UH ∨ x ∈ R) ∧ x ∈ (d.state P).G.E ∧ x ∉ (d.state P).H.E := by
  classical
  let Q : Phase4WS → Prop := fun T => ∀ y ∈ T.copyBuf,
    (y ∈ uhDelFinset UH ∨ y ∈ R) ∧ y ∈ (d.state P).G.E ∧ y ∉ (d.state P).H.E
  have hUH : ∀ T u, u ∈ UH → Q T →
      Q (p4StepUH (d.state P).G.E (d.state P).H.E OS true T u) := by
    intro T u hu hT y hy
    cases u with
    | insert e a b =>
      rcases p4StepEdge_copyBuf_sub hy with h | ⟨h, -⟩
      · exact hT y h
      · exact absurd h (by decide)
    | delete e =>
      rcases p4StepEdge_copyBuf_sub hy with h | ⟨h, rfl⟩
      · exact hT y h
      · simp only [Bool.true_and, decide_eq_true_eq] at h
        refine ⟨Or.inl ?_, h.1, h.2.1⟩
        unfold uhDelFinset
        exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨.delete y, hu, rfl⟩)
    | split a b c f => exact hT y hy
  have hD : ∀ T e, e ∈ D → Q T → Q (p4StepD (d.state P).G.E (d.state P).H.E T e) := by
    intro T e _ hT y hy
    exact hT y (by simpa [p4StepD] using hy)
  have hR : ∀ T e, e ∈ R → Q T → Q (p4StepR (d.state P).G.E (d.state P).H.E true T e) := by
    intro T e he hT y hy
    unfold p4StepR at hy
    split_ifs at hy with hc
    · rcases mem_pushCopy_copyBuf hy with h | rfl
      · exact hT y h
      · exact ⟨Or.inr he, hc.2.1, hc.2.2⟩
    · exact hT y hy
  refine foldl_keeps_mem Q _ R hR _ (foldl_keeps_mem Q _ D hD _
    (foldl_keeps_mem Q _ UH hUH _ ?_)) x hx
  intro y hy
  simp at hy

/-- A sum over a list of distinct elements of a set is at most the sum over the set. -/
theorem list_sum_le_finset_sum {l : List ℕ} {X : Finset ℕ} (f : ℕ → ℕ) (hnd : l.Nodup)
    (hsub : ∀ e ∈ l, e ∈ X) : (l.map f).sum ≤ X.sum f := by
  classical
  rw [← List.sum_toFinset _ hnd]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun e he => hsub e (List.mem_toFinset.mp he))
    (fun _ _ _ => Nat.zero_le _)

/-- The work on a copy buffer of distinct edges of a set `X` is at most the sum of
`p4CopyEdgeCost` over `X`. -/
theorem p4_copy_work_le (P : DSParams) {cap : ℕ} (S : BucketSpannerState cap) (s : ℕ)
    (d' : DSHist) {eL : List ℕ} {X : Finset ℕ} (hnd : eL.Nodup) (hsub : ∀ e ∈ eL, e ∈ X) :
    (eL.map (p4DleftEdgeCost P d')).sum + 142 * slotListCopyWork P S s d' eL ≤
      X.sum (p4CopyEdgeCost P S s d') := by
  have heq : ∀ l : List ℕ, (l.map (p4DleftEdgeCost P d')).sum + 142 * slotListCopyWork P S s d' l =
      (l.map (p4CopyEdgeCost P S s d')).sum := by
    intro l
    induction l with
    | nil => simp [slotListCopyWork]
    | cons e l ih =>
      simp only [slotListCopyWork, List.map_cons, List.sum_cons] at ih ⊢
      rw [← ih]
      unfold p4CopyEdgeCost
      ring
  rw [heq]
  exact list_sum_le_finset_sum _ hnd hsub

end

end MinCostFlow.SparseCore.Program
