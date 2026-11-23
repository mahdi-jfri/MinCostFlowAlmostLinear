module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4TaskFacts

/-!
# The two loops of the spanner part of Phase 4 (`AssemblyFirstStepP4Folds`)

The spanner part of Phase 4 runs one task per touched slot (`p4WVStep`), then scans the new
slots (`p4NewStep`). This file says what the two loops leave in the workspace, from what one
task and one new slot do (`AssemblyFirstStepP4TaskFacts.lean`). It is the first half of `p4SpanWV_cover`: the
second half (`AssemblyFirstStepP4Cover.lean`) puts in the model of the branch step.

* `p4SpanAfter_at_task`: after the tasks, the slot of a task holds the history of its update.
* `P4Eff q d`: task `q` updates its slot, which holds `d`, with a batch that is not empty. Only
  such tasks change the workspace.
* `p4TaskLoop_facts`: when the graphs of the slots fit the sets `A` and `T` of the marks, and the
  graphs of distinct updated slots share no edge, the loop over the tasks keeps the marks right,
  leaves what each updated slot adds (`P4TaskIn`), and adds to `inDtot` and `reemb` only edges
  that come from an updated slot. The graphs must be disjoint because the seen set of the copy
  buffer is kept from one slot to the next: an edge of a slot is copied only if no earlier slot
  saw it.
* `p4NewLoop_facts`: the scan of the new slots keeps the marks right, marks every edge of their
  graphs, and changes neither `inDtot` nor `reemb`.
-/

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.SparseCore MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Read

public section

/-! ## The spanners after the tasks -/

/-- The slots of distinct tasks: a task `t'` on another slot leaves slot `j` alone. -/
theorem p4SpanStep_ne (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap) (mem₀ : ℕ → ℕ)
    (S : BucketSpannerState cap) {t : SpanUpdTask} {j : Fin cap} (hne : t.slot ≠ j.1) :
    p4SpanStep P S6 mem₀ S t j = S j := by
  have h := p4SpanAfter_unchanged P S6 mem₀ (ts := [t]) (j := j)
    (by simp only [List.map_cons, List.map_nil, List.mem_singleton]; exact fun h => hne h.symm) S
  simpa only [List.foldl_cons, List.foldl_nil] using h

/-- **After the tasks**, the slot of a task holds the new history of its update, or keeps its
history when the batch is empty. The slots of the tasks must be distinct. -/
theorem p4SpanAfter_at_task (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) {t : SpanUpdTask} (hs : t.slot < cap) :
    ∀ {ts : List SpanUpdTask}, (ts.map SpanUpdTask.slot).Nodup → t ∈ ts →
    ∀ S : BucketSpannerState cap, ts.foldl (p4SpanStep P S6 mem₀) S ⟨t.slot, hs⟩ =
      p4OnTask S6 mem₀ (S ⟨t.slot, hs⟩) (fun _ _ d => some (p4NewHist P mem₀ d t)) t
  | [], _, ht, _ => absurd ht List.not_mem_nil
  | t' :: ts, hnd, ht, S => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldl_cons]
    by_cases htt : t' = t
    · subst htt
      rw [p4SpanAfter_unchanged P S6 mem₀ (j := ⟨t'.slot, hs⟩) hnd.1]
      unfold p4SpanStep p4OnTask
      simp only [hs, ↓reduceDIte]
      rcases hd : S6 ⟨t'.slot, hs⟩ with _ | d
      · rfl
      · by_cases hb : mem₀ t'.batchPtr = 0
        · simp only [hb, ↓reduceIte]
        · simp only [hb, ↓reduceIte, BucketSpannerState.set, Function.update_self]
    · have ht' : t ∈ ts := (List.mem_cons.mp ht).resolve_left fun h => htt h.symm
      have hne : t'.slot ≠ t.slot := fun h => hnd.1 (h ▸ List.mem_map_of_mem ht')
      rw [p4SpanAfter_at_task P S6 mem₀ hs hnd.2 ht' (p4SpanStep P S6 mem₀ S t'),
        p4SpanStep_ne P S6 mem₀ S (j := ⟨t.slot, hs⟩) hne]

/-! ## The tasks that change the workspace -/

/-- Task `q` updates its slot, whose history before the task is `d`: the slot is in the table, it
holds `d`, and the batch of `q` is not empty. -/
@[expose] def P4Eff {cap : ℕ} (S6 : BucketSpannerState cap) (mem₀ : ℕ → ℕ)
    (q : SpanUpdTask × P4TaskOut) (d : DSHist) : Prop :=
  ∃ hs : q.1.slot < cap, S6 ⟨q.1.slot, hs⟩ = some d ∧ mem₀ q.1.batchPtr ≠ 0

/-- The model state of the slot of task `q` after the task, from the history `d`. -/
noncomputable abbrev p4St (P : DSParams) (mem₀ : ℕ → ℕ) (q : SpanUpdTask × P4TaskOut)
    (d : DSHist) : DynSpannerState P.L :=
  (p4NewHist P mem₀ d q.1).state P

theorem P4Eff.unique {cap : ℕ} {S6 : BucketSpannerState cap} {mem₀ : ℕ → ℕ}
    {q : SpanUpdTask × P4TaskOut} {d d' : DSHist} (h : P4Eff S6 mem₀ q d)
    (h' : P4Eff S6 mem₀ q d') : d' = d := by
  obtain ⟨_, hd, -⟩ := h
  obtain ⟨_, hd', -⟩ := h'
  exact Option.some.inj (hd'.symm.trans hd)

theorem p4WVStep_eff (P : DSParams) {cap : ℕ} {S6 : BucketSpannerState cap} {mem₀ : ℕ → ℕ}
    (OS : Finset ℕ) (A : Phase4WS × EmbView) {q : SpanUpdTask × P4TaskOut} {d : DSHist}
    (h : P4Eff S6 mem₀ q d) :
    (p4WVStep P S6 mem₀ OS A q).1 =
      p4TaskWS P (p4NewHist P mem₀ d q.1) OS q.2.UH q.2.dL q.2.rL A.1 := by
  obtain ⟨hs, hd, hb⟩ := h
  rw [p4WVStep, p4OnTask_of hs hd hb]

theorem p4WVStep_not_eff (P : DSParams) {cap : ℕ} {S6 : BucketSpannerState cap}
    {mem₀ : ℕ → ℕ} (OS : Finset ℕ) (A : Phase4WS × EmbView) {q : SpanUpdTask × P4TaskOut}
    (h : ∀ d, ¬ P4Eff S6 mem₀ q d) : (p4WVStep P S6 mem₀ OS A q).1 = A.1 := by
  rcases p4WVStep_cases P S6 mem₀ OS A q with h' | ⟨hs, d, hd, hb, -⟩
  · exact h'
  · exact absurd ⟨hs, hd, hb⟩ (h d)

/-- What an updated slot adds to the workspace `W` (see `p4TaskWS_facts`). The walk clause has
no condition on the seen set: the loop discharges it, since the graphs of the slots are
disjoint. -/
@[expose] def P4TaskIn (P : DSParams) (mem₀ : ℕ → ℕ) (OS : Finset ℕ)
    (q : SpanUpdTask × P4TaskOut) (d : DSHist) (W : Phase4WS) : Prop :=
  (∀ e ∈ q.2.dL, e ∈ W.inDtot ∧ e ∈ W.delSup ∧ e ∈ W.insSup ∧
    (e ∈ (p4St P mem₀ q d).G.E → e ∈ W.inAct)) ∧
  (∀ e ∈ uhDelFinset q.2.UH, e ∈ W.delSup ∧ (e ∈ (p4St P mem₀ q d).G.E → e ∈ W.inAct)) ∧
  (∀ e ∈ uhInsFinset q.2.UH, e ∈ W.insSup ∧ (e ∈ (p4St P mem₀ q d).G.E → e ∈ W.inAct)) ∧
  (∀ e ∈ q.2.rL, e ∈ W.reemb) ∧
  (∀ e ∈ uhDelFinset q.2.UH, e ∈ (p4St P mem₀ q d).G.E → e ∉ (p4St P mem₀ q d).H.E → e ∈ OS →
    ∀ x ∈ walkEdges (piTotal (p4St P mem₀ q d) e), x ∈ W.inDtot ∧ x ∈ W.delSup ∧
      x ∈ W.insSup ∧ (x ∈ (p4St P mem₀ q d).G.E → x ∈ W.inAct))

theorem P4TaskIn.mono {P : DSParams} {mem₀ : ℕ → ℕ} {OS : Finset ℕ}
    {q : SpanUpdTask × P4TaskOut} {d : DSHist} {W W' : Phase4WS} (h : P4TaskIn P mem₀ OS q d W)
    (hg : P4Grows W W') : P4TaskIn P mem₀ OS q d W' :=
  ⟨fun e he => ⟨hg.1 (h.1 e he).1, hg.2.2.2.1 e (h.1 e he).2.1, hg.2.2.2.2.1 e (h.1 e he).2.2.1,
      fun hG => hg.2.1 ((h.1 e he).2.2.2 hG)⟩,
    fun e he => ⟨hg.2.2.2.1 e (h.2.1 e he).1, fun hG => hg.2.1 ((h.2.1 e he).2 hG)⟩,
    fun e he => ⟨hg.2.2.2.2.1 e (h.2.2.1 e he).1, fun hG => hg.2.1 ((h.2.2.1 e he).2 hG)⟩,
    fun e he => hg.2.2.2.2.2 e (h.2.2.2.1 e he),
    fun e he hG hH hO x hx =>
      ⟨hg.1 (h.2.2.2.2 e he hG hH hO x hx).1, hg.2.2.2.1 x (h.2.2.2.2 e he hG hH hO x hx).2.1,
        hg.2.2.2.2.1 x (h.2.2.2.2 e he hG hH hO x hx).2.2.1,
        fun hxG => hg.2.1 ((h.2.2.2.2 e he hG hH hO x hx).2.2.2 hxG)⟩⟩

/-! ## The list `reemb` -/

theorem p4StepEdge_reemb {GE HE : Finset ℕ} {fD fDel fIns fCopy : Bool} {S : Phase4WS} {e : ℕ} :
    (p4StepEdge GE HE fD fDel fIns fCopy S e).reemb = S.reemb := by
  have h1 := (p4StepEdge_false_fields GE HE fD fDel fIns S e).2.2.2.2.2.1
  cases fCopy with
  | false => exact h1
  | true => rw [p4StepEdge_true, (pushCopy_fields _ e).2.2.2.2.2.1, h1]

theorem p4StepUH_reemb {GE HE OS : Finset ℕ} {isOld : Bool} {S : Phase4WS} {u : Update} :
    (p4StepUH GE HE OS isOld S u).reemb = S.reemb := by
  cases u with
  | insert e a b => exact p4StepEdge_reemb
  | delete e => exact p4StepEdge_reemb
  | split a b c d => rfl

theorem p4StepDleft_reemb {GE HE OS : Finset ℕ} {walk : ℕ → List (ℕ × Bool)} {S : Phase4WS}
    {e : ℕ} : (p4StepDleft GE HE OS walk S e).reemb = S.reemb := by
  classical
  unfold p4StepDleft
  split_ifs
  · exact foldl_keeps (fun T => T.reemb = S.reemb) _
      (fun T x h => by rw [p4StepEdge_reemb]; exact h) _ S rfl
  · rfl

/-- A task adds to `reemb` only the edges of its list `R`. -/
theorem p4TaskWS_reemb (P : DSParams) (d : DSHist) (OS : Finset ℕ) (UH : List Update)
    (D R : List ℕ) (S : Phase4WS) :
    ∀ x ∈ (p4TaskWS P d OS UH D R S).reemb, x ∈ S.reemb ∨ x ∈ R := by
  classical
  set GE := (d.state P).G.E
  set HE := (d.state P).H.E
  let Q : Phase4WS → Prop := fun T => ∀ x ∈ T.reemb, x ∈ S.reemb ∨ x ∈ R
  have h₀ : Q { S with copyBuf := [] } := fun x hx => Or.inl hx
  have h₁ := foldl_keeps Q (p4StepUH GE HE OS true) (fun T u h x hx => by
    rw [p4StepUH_reemb] at hx; exact h x hx) UH _ h₀
  have h₂ := foldl_keeps Q (p4StepD GE HE) (fun T e h => h) D _ h₁
  have h₃ := foldl_keeps_mem Q (p4StepR GE HE true) R (fun T e he h x hx => by
    rw [(p4StepR_fields GE HE true T e).2.2.2.2.2.1, mem_pushDedup_iff] at hx
    rcases hx with hx | rfl
    · exact h x hx
    · exact Or.inr he) _ h₂
  exact foldl_keeps Q (p4StepDleft GE HE OS (piTotal (d.state P)))
    (fun T e h x hx => by rw [p4StepDleft_reemb] at hx; exact h x hx) _ _ h₃

/-- The scan of a new slot leaves `reemb`. -/
theorem p4NewScan_reemb (HE : Finset ℕ) (l : List ℕ) (S : Phase4WS) :
    (l.foldl (p4StepNew HE) { S with copyBuf := [] }).reemb = S.reemb :=
  foldl_keeps (fun T => T.reemb = S.reemb) _
    (fun T e h => by rw [(p4StepNew_fields HE T e).2.2.2.2.2.1]; exact h) l _ rfl

/-! ## The loop over the tasks -/

set_option maxHeartbeats 800000 in
/-- **What the loop over the tasks leaves in the workspace.** The hypotheses: the graph and the
spanner of each updated slot fit the sets `A` and `T` of the marks, the graphs of distinct
updated slots are disjoint, and the start workspace saw no edge of these graphs. -/
theorem p4TaskLoop_facts (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap) (mem₀ : ℕ → ℕ)
    (OS A T : Finset ℕ) :
    ∀ (qs : List (SpanUpdTask × P4TaskOut)) (S : Phase4WS) (v : EmbView),
    (∀ q ∈ qs, ∀ d, P4Eff S6 mem₀ q d →
      P4SlotFits A T (p4St P mem₀ q d).G.E (p4St P mem₀ q d).H.E) →
    qs.Pairwise (fun q₁ q₂ => ∀ d₁ d₂, P4Eff S6 mem₀ q₁ d₁ → P4Eff S6 mem₀ q₂ d₂ →
      Disjoint (p4St P mem₀ q₁ d₁).G.E (p4St P mem₀ q₂ d₂).G.E) →
    (∀ q ∈ qs, ∀ d, P4Eff S6 mem₀ q d → Disjoint S.seenCopy (p4St P mem₀ q d).G.E) →
    P4MarkOK A T S →
    P4Grows S (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v)).1 ∧
    P4MarkOK A T (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v)).1 ∧
    (∀ q ∈ qs, ∀ d, P4Eff S6 mem₀ q d →
      P4TaskIn P mem₀ OS q d (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v)).1) ∧
    (∀ x ∈ (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v)).1.inDtot, x ∈ S.inDtot ∨
      ∃ q ∈ qs, ∃ d, P4Eff S6 mem₀ q d ∧ (x ∈ q.2.dL ∨
        ∃ e ∈ ((p4St P mem₀ q d).G.E \ (p4St P mem₀ q d).H.E) ∩ OS,
          x ∈ walkEdges (piTotal (p4St P mem₀ q d) e))) ∧
    (∀ x ∈ (qs.foldl (p4WVStep P S6 mem₀ OS) (S, v)).1.reemb, x ∈ S.reemb ∨
      ∃ q ∈ qs, ∃ d, P4Eff S6 mem₀ q d ∧ x ∈ q.2.rL) := by
  intro qs
  induction qs with
  | nil =>
    intro S v _ _ _ hS
    exact ⟨P4Grows.refl S, hS, fun q hq => absurd hq List.not_mem_nil, fun x hx => Or.inl hx,
      fun x hx => Or.inl hx⟩
  | cons q qs ih =>
    intro S v hfit hpw hseen hS
    rw [List.pairwise_cons] at hpw
    rw [List.foldl_cons]
    set A₁ := p4WVStep P S6 mem₀ OS (S, v) q with hA₁
    have hfold : qs.foldl (p4WVStep P S6 mem₀ OS) A₁ =
        qs.foldl (p4WVStep P S6 mem₀ OS) (A₁.1, A₁.2) := rfl
    rw [hfold]
    by_cases heff : ∃ d, P4Eff S6 mem₀ q d
    · obtain ⟨d, hd⟩ := heff
      have h1 : A₁.1 = p4TaskWS P (p4NewHist P mem₀ d q.1) OS q.2.UH q.2.dL q.2.rL S :=
        p4WVStep_eff P OS (S, v) hd
      have hF := p4TaskWS_facts P (p4NewHist P mem₀ d q.1) OS q.2.UH q.2.dL q.2.rL S
      have hRm := p4TaskWS_reemb P (p4NewHist P mem₀ d q.1) OS q.2.UH q.2.dL q.2.rL S
      have hMk := p4MarkOK_taskWS P (p4NewHist P mem₀ d q.1) OS q.2.UH q.2.dL q.2.rL
        (hfit q List.mem_cons_self d hd) hS
      rw [← h1] at hF hRm hMk
      obtain ⟨g, hDadd, hUHd, hUHi, hR, hW, hdt, hsc⟩ := hF
      have hseen₁ : ∀ q' ∈ qs, ∀ d', P4Eff S6 mem₀ q' d' →
          Disjoint A₁.1.seenCopy (p4St P mem₀ q' d').G.E := fun q' hq' d' hd' =>
        Finset.disjoint_of_subset_left hsc (Finset.disjoint_union_left.mpr
          ⟨hseen q' (List.mem_cons_of_mem _ hq') d' hd', hpw.1 q' hq' d d' hd hd'⟩)
      obtain ⟨ig, imk, iin, idt, irm⟩ := ih A₁.1 A₁.2
        (fun q' hq' => hfit q' (List.mem_cons_of_mem _ hq')) hpw.2 hseen₁ hMk
      refine ⟨g.trans ig, imk, fun q' hq' d' hd' => ?_, fun x hx => ?_, fun x hx => ?_⟩
      · rcases List.mem_cons.mp hq' with rfl | hq'
        · have hdd := hd.unique hd'
          subst hdd
          have hdisj := hseen q' List.mem_cons_self d' hd'
          refine P4TaskIn.mono ⟨hDadd, hUHd, hUHi, hR, fun e he hG hH hO x hx => ?_⟩ ig
          exact hW e he hG hH hO (Finset.disjoint_right.mp hdisj hG) x hx
        · exact iin q' hq' d' hd'
      · rcases idt x hx with h | ⟨q', hq', d', hd', h⟩
        · rcases Finset.mem_union.mp (hdt h) with h | h
          · rcases Finset.mem_union.mp h with h | h
            · exact Or.inl h
            · exact Or.inr ⟨q, List.mem_cons_self, d, hd, Or.inl (List.mem_toFinset.mp h)⟩
          · obtain ⟨e, he, hx⟩ := Finset.mem_biUnion.mp h
            exact Or.inr ⟨q, List.mem_cons_self, d, hd, Or.inr ⟨e, he, hx⟩⟩
        · exact Or.inr ⟨q', List.mem_cons_of_mem _ hq', d', hd', h⟩
      · rcases irm x hx with h | ⟨q', hq', d', hd', h⟩
        · rcases hRm x h with h | h
          · exact Or.inl h
          · exact Or.inr ⟨q, List.mem_cons_self, d, hd, h⟩
        · exact Or.inr ⟨q', List.mem_cons_of_mem _ hq', d', hd', h⟩
    · have hne : ∀ d, ¬ P4Eff S6 mem₀ q d := fun d h => heff ⟨d, h⟩
      have h1 : A₁.1 = S := p4WVStep_not_eff P OS (S, v) hne
      have hseen₁ : ∀ q' ∈ qs, ∀ d', P4Eff S6 mem₀ q' d' →
          Disjoint A₁.1.seenCopy (p4St P mem₀ q' d').G.E := fun q' hq' d' hd' =>
        h1 ▸ hseen q' (List.mem_cons_of_mem _ hq') d' hd'
      obtain ⟨ig, imk, iin, idt, irm⟩ := ih A₁.1 A₁.2
        (fun q' hq' => hfit q' (List.mem_cons_of_mem _ hq')) hpw.2 hseen₁ (h1 ▸ hS)
      have g : P4Grows S A₁.1 := by rw [h1]; exact P4Grows.refl S
      refine ⟨g.trans ig, imk, fun q' hq' d' hd' => ?_, fun x hx => ?_, fun x hx => ?_⟩
      · rcases List.mem_cons.mp hq' with rfl | hq'
        · exact absurd hd' (hne d')
        · exact iin q' hq' d' hd'
      · rcases idt x hx with h | ⟨q', hq', d', hd', h⟩
        · rw [h1] at h; exact Or.inl h
        · exact Or.inr ⟨q', List.mem_cons_of_mem _ hq', d', hd', h⟩
      · rcases irm x hx with h | ⟨q', hq', d', hd', h⟩
        · rw [h1] at h; exact Or.inl h
        · exact Or.inr ⟨q', List.mem_cons_of_mem _ hq', d', hd', h⟩

/-! ## The loop over the new slots -/

theorem p4NewStep_some (P : DSParams) {cap : ℕ} {S7 : BucketSpannerState cap}
    (A : Phase4WS × EmbView) {q : ℕ × List ℕ} (hs : q.1 < cap) {d : DSHist}
    (hd : S7 ⟨q.1, hs⟩ = some d) :
    (p4NewStep P S7 A q).1 = q.2.foldl (p4StepNew (d.state P).H.E) { A.1 with copyBuf := [] } := by
  simp only [p4NewStep, hs, ↓reduceDIte, hd]

theorem p4NewStep_none (P : DSParams) {cap : ℕ} {S7 : BucketSpannerState cap}
    (A : Phase4WS × EmbView) {q : ℕ × List ℕ} (h : ∀ (hs : q.1 < cap), S7 ⟨q.1, hs⟩ = none) :
    (p4NewStep P S7 A q).1 = A.1 := by
  rcases p4NewStep_cases P S7 A q with h' | ⟨hs, d, hd, -⟩
  · exact h'
  · rw [h hs] at hd; cases hd

/-- **What the scan of the new slots leaves in the workspace.** When the graph and the spanner of
each new slot fit `A` and `T`, and its list holds edges of its graph, the marks stay right, every
edge of the lists is marked, and `inDtot` and `reemb` do not change. -/
theorem p4NewLoop_facts (P : DSParams) {cap : ℕ} (S7 : BucketSpannerState cap)
    (A T : Finset ℕ) :
    ∀ (ns : List (ℕ × List ℕ)) (S : Phase4WS) (v : EmbView),
    (∀ q ∈ ns, ∀ (hs : q.1 < cap) (d : DSHist), S7 ⟨q.1, hs⟩ = some d →
      P4SlotFits A T (d.state P).G.E (d.state P).H.E ∧ ∀ e ∈ q.2, e ∈ (d.state P).G.E) →
    P4MarkOK A T S →
    P4Grows S (ns.foldl (p4NewStep P S7) (S, v)).1 ∧
    P4MarkOK A T (ns.foldl (p4NewStep P S7) (S, v)).1 ∧
    (∀ q ∈ ns, ∀ (hs : q.1 < cap) (d : DSHist), S7 ⟨q.1, hs⟩ = some d → ∀ e ∈ q.2,
      e ∈ (ns.foldl (p4NewStep P S7) (S, v)).1.inAct) ∧
    (ns.foldl (p4NewStep P S7) (S, v)).1.inDtot = S.inDtot ∧
    (ns.foldl (p4NewStep P S7) (S, v)).1.reemb = S.reemb := by
  intro ns
  induction ns with
  | nil =>
    intro S v _ hS
    exact ⟨P4Grows.refl S, hS, fun q hq => absurd hq List.not_mem_nil, rfl, rfl⟩
  | cons q ns ih =>
    intro S v hfit hS
    rw [List.foldl_cons]
    set A₁ := p4NewStep P S7 (S, v) q with hA₁
    have hfold : ns.foldl (p4NewStep P S7) A₁ = ns.foldl (p4NewStep P S7) (A₁.1, A₁.2) := rfl
    rw [hfold]
    by_cases hsome : ∃ (hs : q.1 < cap) (d : DSHist), S7 ⟨q.1, hs⟩ = some d
    · obtain ⟨hs, d, hd⟩ := hsome
      have h1 := p4NewStep_some P (S, v) hs hd
      obtain ⟨hfq, hlq⟩ := hfit q List.mem_cons_self hs d hd
      obtain ⟨g, hadd, hdt, -⟩ := p4NewScan_facts (d.state P).H.E q.2 S
      have hmk := p4MarkOK_newScan hfq hlq hS
      have hrm := p4NewScan_reemb (d.state P).H.E q.2 S
      rw [← h1] at g hadd hdt hmk hrm
      obtain ⟨ig, imk, iin, idt, irm⟩ := ih A₁.1 A₁.2
        (fun q' hq' => hfit q' (List.mem_cons_of_mem _ hq')) hmk
      refine ⟨g.trans ig, imk, fun q' hq' hs' d' hd' e he => ?_, idt.trans hdt, irm.trans hrm⟩
      rcases List.mem_cons.mp hq' with rfl | hq'
      · have hdd : d' = d := Option.some.inj (hd'.symm.trans hd)
        subst hdd
        exact ig.2.1 (hadd e he).1
      · exact iin q' hq' hs' d' hd' e he
    · have hnone : ∀ (hs : q.1 < cap), S7 ⟨q.1, hs⟩ = none := fun hs => by
        rcases h : S7 ⟨q.1, hs⟩ with _ | d
        · rfl
        · exact absurd ⟨hs, d, h⟩ hsome
      have h1 : A₁.1 = S := p4NewStep_none P (S, v) hnone
      obtain ⟨ig, imk, iin, idt, irm⟩ := ih A₁.1 A₁.2
        (fun q' hq' => hfit q' (List.mem_cons_of_mem _ hq')) (h1 ▸ hS)
      have g : P4Grows S A₁.1 := by rw [h1]; exact P4Grows.refl S
      refine ⟨g.trans ig, imk, fun q' hq' hs' d' hd' e he => ?_,
        idt.trans (congrArg Phase4WS.inDtot h1), irm.trans (congrArg Phase4WS.reemb h1)⟩
      rcases List.mem_cons.mp hq' with rfl | hq'
      · rw [hnone hs'] at hd'; cases hd'
      · exact iin q' hq' hs' d' hd' e he

end

end MinCostFlow.SparseCore.Program
