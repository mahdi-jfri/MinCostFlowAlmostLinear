module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4Cover
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4New
public import MinCostFlow.SparseCore.Program.AssemblyFirstEmbCopyIns

import Mathlib.Tactic

/-!
# The embedding view of Phase 4, edge by edge (`AssemblyFirstStepEmbFold`)

Phase 4 changes the view of the embedding table in three ways: each task writes the walks of the
edges of its copy buffer, each new slot writes the walks of the edges of its copy buffer, and at
the end every entering edge gets the walk `[(e, true)]` (`p4SpanWV`, `insSelfChange`). We want to
know, for each edge, whether its entry changed and, if so, what it holds.

The tool is the seen set of the workspace. An edge goes into a copy buffer only once in the whole
phase, and when it does, it goes into the seen set too (`pushCopy`). Each copy buffer is written
right after its scan. So the edges whose entry changed are exactly the seen edges, and an edge
keeps its old entry when it is never seen. The invariant `EmbViewInv` says this for a view, a
set `W` of written edges, and the walks `g` that the writes put.

* `EmbViewInv.apply`: a change list that writes the walk `g e` at each edge `e` it names keeps the
  invariant, with `W` grown by the edges of the list.
* `p4SpanWV_viewInv`: after the tasks and the new slots, the invariant holds with `W` the seen
  set, when every walk written is the walk `g` asks for.
* `p4SpanWV_seen_task`, `p4SpanWV_seen_new`: which edges the seen set holds at the end.
-/

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.SparseCore MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Read

@[expose] public section

/-- A change list `X` writes the walk `g e` at each edge `e` that it names. -/
def EmbGood (g : Embedding) (X : EmbChange) : Prop := ∀ x ∈ X, x.2 = g x.1

/-- **The view `v` is the view `v₀` with the walks `g` written on the edges `W`**: `v` covers the
domain of `v₀`, it agrees with `v₀` off `W`, and it holds `g e` at each edge `e` of `W`. -/
def EmbViewInv (v₀ : EmbView) (g : Embedding) (W : Finset ℕ) (v : EmbView) : Prop :=
  v₀.dom ⊆ v.dom ∧ (∀ e, e ∉ W → v.emb e = v₀.emb e) ∧ ∀ e ∈ W, e ∈ v.dom ∧ v.emb e = g e

end

public section

/-- A change list keeps the walk of an edge that it does not name. -/
theorem foldl_embUpd_not_mem :
    ∀ (X : EmbChange) (f : Embedding) {e : ℕ}, e ∉ X.map Prod.fst → X.foldl embUpd f e = f e
  | [], _, _, _ => rfl
  | x :: X, f, e, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [List.foldl_cons, foldl_embUpd_not_mem X _ h.2]
    exact Function.update_of_ne h.1 _ _

/-- A change list that writes `g` holds `g e` at each edge `e` that it names. -/
theorem foldl_embUpd_good {g : Embedding} :
    ∀ (X : EmbChange) (f : Embedding), EmbGood g X → ∀ e ∈ X.map Prod.fst,
      X.foldl embUpd f e = g e
  | [], _, _, e, he => by simp at he
  | x :: X, f, hX, e, he => by
    rw [List.foldl_cons]
    by_cases hm : e ∈ X.map Prod.fst
    · exact foldl_embUpd_good X _ (fun y hy => hX y (List.mem_cons_of_mem _ hy)) e hm
    · rw [foldl_embUpd_not_mem X _ hm]
      have hex : e = x.1 := by
        simp only [List.map_cons, List.mem_cons] at he
        exact he.resolve_right hm
      subst hex
      rw [embUpd, Function.update_self]
      exact hX x List.mem_cons_self

/-- The invariant holds at the start, with nothing written. -/
theorem EmbViewInv.start (v₀ : EmbView) (g : Embedding) : EmbViewInv v₀ g ∅ v₀ :=
  ⟨subset_rfl, fun _ _ => rfl, fun e he => absurd he (Finset.notMem_empty e)⟩

/-- **A change list that writes `g` keeps the invariant**, for a new set of written edges `W'`
that holds `W` and the edges of the list, and no other edges. -/
theorem EmbViewInv.apply {v₀ : EmbView} {g : Embedding} {W : Finset ℕ} {v : EmbView}
    (h : EmbViewInv v₀ g W v) {X : EmbChange} (hX : EmbGood g X) {W' : Finset ℕ}
    (hW' : ∀ e ∈ W', e ∈ W ∨ e ∈ X.map Prod.fst) (hW : W ⊆ W')
    (hXW : ∀ e ∈ X.map Prod.fst, e ∈ W') : EmbViewInv v₀ g W' (v.apply X) := by
  classical
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.trans Finset.subset_union_left, fun e he => ?_, fun e he => ?_⟩
  · have hnX : e ∉ X.map Prod.fst := fun hm => he (hXW e hm)
    show X.foldl embUpd v.emb e = _
    rw [foldl_embUpd_not_mem X _ hnX]
    exact h2 e (fun hw => he (hW hw))
  · show e ∈ v.dom ∪ (X.map Prod.fst).toFinset ∧ X.foldl embUpd v.emb e = g e
    by_cases hm : e ∈ X.map Prod.fst
    · exact ⟨Finset.mem_union_right _ (List.mem_toFinset.mpr hm), foldl_embUpd_good X _ hX e hm⟩
    · have hw : e ∈ W := (hW' e he).resolve_right hm
      rw [foldl_embUpd_not_mem X _ hm]
      exact ⟨Finset.mem_union_left _ (h3 e hw).1, (h3 e hw).2⟩

/-- An edge is seen after it is pushed into the copy buffer. -/
theorem mem_pushCopy_seenCopy (S : Phase4WS) (e : ℕ) : e ∈ (pushCopy S e).seenCopy := by
  classical
  unfold pushCopy
  split_ifs with h
  · exact h
  · exact Finset.mem_insert_self e _

/-- The step of a new slot copies only through `pushCopy`. -/
theorem copyStep_stepNew (HE : Finset ℕ) (e : ℕ) : CopyStep fun T => p4StepNew HE T e := by
  classical
  intro S₀ T h
  dsimp only
  have key : ∀ T' : Phase4WS, T'.seenCopy = T.seenCopy → T'.copyBuf = T.copyBuf →
      CopyInv S₀ (if e ∉ HE then pushCopy T' e else T') ∧
        ∀ x ∈ T.copyBuf, x ∈ (if e ∉ HE then pushCopy T' e else T').copyBuf := by
    intro T' hs hc
    have h1 : CopyInv S₀ T' := fun x hx => by rw [hc]; exact h x (hs ▸ hx)
    by_cases hc' : e ∈ HE
    · rw [if_neg (not_not.mpr hc')]
      exact ⟨h1, fun _ hx => hc ▸ hx⟩
    · rw [if_pos hc']
      exact ⟨(copyInv_pushCopy h1 e).1, fun x hx => (copyInv_pushCopy h1 e).2.1 x (hc ▸ hx)⟩
  exact key _ rfl rfl

/-- The step of an edge of the copy buffer on its walk copies nothing. -/
theorem copyStep_stepDleft (GE HE OS : Finset ℕ) (walk : ℕ → List (ℕ × Bool)) (e : ℕ) :
    CopyStep fun T => p4StepDleft GE HE OS walk T e := by
  classical
  intro S₀ T h
  dsimp only
  unfold p4StepDleft
  split_ifs
  · exact copyStep_foldl _ (fun x => copyStep_stepEdge GE HE true true true false x) _ S₀ T h
  · exact ⟨h, fun _ hx => hx⟩

/-- **The scans of a task**: every edge seen after the scans was seen before or is in the copy
buffer, and every edge of the copy buffer is seen. -/
theorem p4TaskScan_copy (P : DSParams) (d : DSHist) (OS : Finset ℕ) (UH : List Update)
    (D R : List ℕ) (S : Phase4WS) :
    CopyInv S (p4TaskScan P d OS UH D R S) ∧ CopyBufOK (p4TaskScan P d OS UH D R S) := by
  classical
  refine ⟨?_, ?_⟩
  · have h0 : CopyInv S { S with copyBuf := [] } := fun x hx => Or.inl hx
    have h1 := (copyStep_foldl _ (fun u => copyStep_stepUH (d.state P).G.E (d.state P).H.E OS
      true u) UH) S _ h0
    have h2 := (copyStep_foldl _ (fun e => copyStep_stepD (d.state P).G.E (d.state P).H.E e) D)
      S _ h1.1
    exact ((copyStep_foldl _ (fun e => copyStep_stepR (d.state P).G.E (d.state P).H.E true e) R)
      S _ h2.1).1
  · have hUH : ∀ T u, CopyBufOK T →
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
    exact foldl_keeps CopyBufOK _ hR R _ (foldl_keeps CopyBufOK _ hD D _
      (foldl_keeps CopyBufOK _ hUH UH _ ⟨List.nodup_nil, fun _ h => (by cases h)⟩))

/-- **What a task does to the seen set**: the seen set after the task is the seen set before it
with the copy buffer of the scans added. -/
theorem p4TaskWS_seen (P : DSParams) (d : DSHist) (OS : Finset ℕ) (UH : List Update)
    (D R : List ℕ) (S : Phase4WS) :
    (∀ e ∈ (p4TaskWS P d OS UH D R S).seenCopy,
      e ∈ S.seenCopy ∨ e ∈ (p4TaskScan P d OS UH D R S).copyBuf) ∧
    S.seenCopy ⊆ (p4TaskWS P d OS UH D R S).seenCopy ∧
    ∀ e ∈ (p4TaskScan P d OS UH D R S).copyBuf, e ∈ (p4TaskWS P d OS UH D R S).seenCopy := by
  obtain ⟨hI, hOK⟩ := p4TaskScan_copy P d OS UH D R S
  have hD := (copyStep_foldl _ (fun e => copyStep_stepDleft (d.state P).G.E (d.state P).H.E OS
    (piTotal (d.state P)) e) (p4TaskScan P d OS UH D R S).copyBuf) S _ hI
  have hG : P4Grows (p4TaskScan P d OS UH D R S) (p4TaskWS P d OS UH D R S) :=
    foldl_grows _ _ (fun T e _ => p4Grows_stepDleft _ _ _ _ T e) _
  refine ⟨fun e he => ?_, (p4TaskWS_facts P d OS UH D R S).1.2.2.1, fun e he => hG.2.2.1 (hOK.2 e he)⟩
  rcases hD.1 e he with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [← p4TaskWS_copyBuf P d OS UH D R S]; exact h)

/-- **What a new slot does to the seen set**: the seen set after the slot is the seen set before
it with the copy buffer of the slot added. -/
theorem p4NewScan_seen (HE : Finset ℕ) (l : List ℕ) (S : Phase4WS) :
    (∀ e ∈ (l.foldl (p4StepNew HE) { S with copyBuf := [] }).seenCopy,
      e ∈ S.seenCopy ∨ e ∈ (l.foldl (p4StepNew HE) { S with copyBuf := [] }).copyBuf) ∧
    S.seenCopy ⊆ (l.foldl (p4StepNew HE) { S with copyBuf := [] }).seenCopy ∧
    ∀ e ∈ (l.foldl (p4StepNew HE) { S with copyBuf := [] }).copyBuf,
      e ∈ (l.foldl (p4StepNew HE) { S with copyBuf := [] }).seenCopy := by
  classical
  have h0 : CopyInv S { S with copyBuf := [] } := fun x hx => Or.inl hx
  have hI := ((copyStep_foldl _ (fun e => copyStep_stepNew HE e) l) S _ h0).1
  have hOK : CopyBufOK (l.foldl (p4StepNew HE) { S with copyBuf := [] }) := by
    refine foldl_keeps CopyBufOK _ (fun T e hT => ?_) l _ ⟨List.nodup_nil, fun _ h => by cases h⟩
    have key : ∀ T' : Phase4WS, T'.seenCopy = T.seenCopy → T'.copyBuf = T.copyBuf →
        CopyBufOK (if e ∉ HE then pushCopy T' e else T') := by
      intro T' hs hc
      have h1 : CopyBufOK T' := copyBufOK_of_eq hT hc hs
      by_cases hc' : e ∈ HE
      · rw [if_neg (not_not.mpr hc')]
        exact h1
      · rw [if_pos hc']
        exact copyBufOK_pushCopy h1 e
    exact key _ rfl rfl
  exact ⟨hI, (p4NewScan_facts HE l S).1.2.2.1, hOK.2⟩


/-! ## Folds -/

/-- A fold keeps a property that each step with an element of the list keeps. -/
theorem foldl_pair_keeps {α β : Type} (Q : β → Prop) (f : β → α → β) :
    ∀ (l : List α) (b : β), (∀ b a, a ∈ l → Q b → Q (f b a)) → Q b → Q (l.foldl f b)
  | [], _, _, hb => hb
  | a :: l, b, hf, hb => foldl_pair_keeps Q f l (f b a)
      (fun b' a' ha' => hf b' a' (List.mem_cons_of_mem _ ha')) (hf b a List.mem_cons_self hb)

/-- A fold of steps that grow a set grows it. -/
theorem foldl_set_mono {α β : Type} (s : β → Finset ℕ) (f : β → α → β)
    (hf : ∀ b a, s b ⊆ s (f b a)) : ∀ (l : List α) (b : β), s b ⊆ s (l.foldl f b)
  | [], _ => subset_rfl
  | a :: l, b => (hf b a).trans (foldl_set_mono s f hf l (f b a))

/-- In a fold of steps that grow a set, an edge that the step of one element always puts into
the set is in the set at the end. -/
theorem foldl_set_mem {α β : Type} (s : β → Finset ℕ) (f : β → α → β)
    (hf : ∀ b a, s b ⊆ s (f b a)) {e : ℕ} {a₀ : α} (ha : ∀ b, e ∈ s (f b a₀)) :
    ∀ (l : List α) (b : β), a₀ ∈ l → e ∈ s (l.foldl f b)
  | [], _, h => absurd h List.not_mem_nil
  | a :: l, b, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact foldl_set_mono s f hf l _ (ha b)
    · exact foldl_set_mem s f hf ha l _ h

/-! ## The view after the tasks and the new slots -/

/-- The edges named by `slotChange` are its list. -/
theorem slotChange_map_fst (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap) (s : ℕ)
    (es : List ℕ) : (slotChange P S6 s es).map Prod.fst = es := by
  unfold slotChange
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.map_cons, ih]

/-- The walk of a slot that holds `d`, at an edge outside its spanner, is the walk of `d`. -/
theorem slotWalk_of_not_mem (P : DSParams) {cap : ℕ} {S6 : BucketSpannerState cap} {s : ℕ}
    (hs : s < cap) {d : DSHist} (hd : S6 ⟨s, hs⟩ = some d) {e : ℕ} (he : e ∉ (d.state P).H.E) :
    slotWalk P S6 s e = piTotal (d.state P) e := by
  simp only [slotWalk, hs, ↓reduceDIte, hd, he, ↓reduceIte]

/-- A task keeps the invariant with the seen set as the written edges, when the walks of its new
history outside its spanner are those of `g`. -/
theorem p4WVStep_viewInv (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) (OS : Finset ℕ) (v₀ : EmbView) (g : Embedding)
    (q : SpanUpdTask × P4TaskOut)
    (hT : ∀ (hs : q.1.slot < cap) (d : DSHist), S6 ⟨q.1.slot, hs⟩ = some d →
      mem₀ q.1.batchPtr ≠ 0 → ∀ e ∈ ((p4NewHist P mem₀ d q.1).state P).G.E,
        e ∉ ((p4NewHist P mem₀ d q.1).state P).H.E →
        piTotal ((p4NewHist P mem₀ d q.1).state P) e = g e)
    (A : Phase4WS × EmbView) (hA : EmbViewInv v₀ g A.1.seenCopy A.2) :
    EmbViewInv v₀ g (p4WVStep P S6 mem₀ OS A q).1.seenCopy (p4WVStep P S6 mem₀ OS A q).2 := by
  by_cases hs : q.1.slot < cap
  · cases hd : S6 ⟨q.1.slot, hs⟩ with
    | none => simp only [p4WVStep, p4OnTask, hs, ↓reduceDIte, hd]; exact hA
    | some d =>
      by_cases hb : mem₀ q.1.batchPtr = 0
      · rw [p4WVStep, p4OnTask_empty hs hd hb]; exact hA
      · rw [p4WVStep, p4OnTask_of hs hd hb]
        obtain ⟨h1, h2, h3⟩ := p4TaskWS_seen P (p4NewHist P mem₀ d q.1) OS q.2.UH q.2.dL q.2.rL A.1
        refine hA.apply (fun x hx => ?_) (fun e he => ?_) h2 (fun e he => ?_)
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
          obtain ⟨-, hG, hH⟩ := mem_p4TaskScan_copyBuf_cand he
          have hset : (S6.set ⟨q.1.slot, hs⟩ (some (p4NewHist P mem₀ d q.1))) ⟨q.1.slot, hs⟩ =
              some (p4NewHist P mem₀ d q.1) := by simp [BucketSpannerState.set]
          rw [slotWalk_of_not_mem P hs hset hH]
          exact hT hs d hd hb e hG hH
        · rw [slotChange_map_fst]; exact h1 e he
        · rw [slotChange_map_fst] at he; exact h3 e he
  · simp only [p4WVStep, p4OnTask, hs, ↓reduceDIte]; exact hA

/-- A new slot keeps the invariant with the seen set as the written edges, when the walks of its
history at the edges of its list outside its spanner are those of `g`. -/
theorem p4NewStep_viewInv (P : DSParams) {cap : ℕ} (S' : BucketSpannerState cap)
    (v₀ : EmbView) (g : Embedding) (q : ℕ × List ℕ)
    (hN : ∀ (hs : q.1 < cap) (d : DSHist), S' ⟨q.1, hs⟩ = some d →
      ∀ e ∈ q.2, e ∉ (d.state P).H.E → piTotal (d.state P) e = g e)
    (A : Phase4WS × EmbView) (hA : EmbViewInv v₀ g A.1.seenCopy A.2) :
    EmbViewInv v₀ g (p4NewStep P S' A q).1.seenCopy (p4NewStep P S' A q).2 := by
  by_cases hs : q.1 < cap
  · cases hd : S' ⟨q.1, hs⟩ with
    | none => simp only [p4NewStep, hs, ↓reduceDIte, hd]; exact hA
    | some d =>
      simp only [p4NewStep, hs, ↓reduceDIte, hd]
      obtain ⟨h1, h2, h3⟩ := p4NewScan_seen (d.state P).H.E q.2 A.1
      refine hA.apply (fun x hx => ?_) (fun e he => ?_) h2 (fun e he => ?_)
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
        obtain ⟨hq, hH⟩ := (p4StepNew_copyBuf (d.state P).H.E q.2 A.1).2 e he
        rw [slotWalk_of_not_mem P hs hd hH]
        exact hN hs d hd e hq hH
      · rw [slotChange_map_fst]; exact h1 e he
      · rw [slotChange_map_fst] at he; exact h3 e he
  · simp only [p4NewStep, hs, ↓reduceDIte]; exact hA

/-- **The view after the tasks and the new slots** is the start view with the walks of `g`
written on the seen edges, when every walk that a task or a new slot writes is that of `g`. -/
theorem p4SpanWV_viewInv (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) (OS : Finset ℕ) (v₀ : EmbView) (g : Embedding)
    (qs : List (SpanUpdTask × P4TaskOut)) (ns : List (ℕ × List ℕ))
    (hT : ∀ q ∈ qs, ∀ (hs : q.1.slot < cap) (d : DSHist), S6 ⟨q.1.slot, hs⟩ = some d →
      mem₀ q.1.batchPtr ≠ 0 → ∀ e ∈ ((p4NewHist P mem₀ d q.1).state P).G.E,
        e ∉ ((p4NewHist P mem₀ d q.1).state P).H.E →
        piTotal ((p4NewHist P mem₀ d q.1).state P) e = g e)
    (hN : ∀ q ∈ ns, ∀ (hs : q.1 < cap) (d : DSHist),
      p4SpanAfter P S6 mem₀ (qs.map Prod.fst) ⟨q.1, hs⟩ = some d →
      ∀ e ∈ q.2, e ∉ (d.state P).H.E → piTotal (d.state P) e = g e) :
    EmbViewInv v₀ g (p4SpanWV P S6 mem₀ OS v₀ (qs.map Prod.fst) qs ns).1.seenCopy
      (p4SpanWV P S6 mem₀ OS v₀ (qs.map Prod.fst) qs ns).2 := by
  unfold p4SpanWV
  refine foldl_pair_keeps (fun A => EmbViewInv v₀ g A.1.seenCopy A.2) _ ns _
    (fun A q hq hA => p4NewStep_viewInv P _ v₀ g q (hN q hq) A hA) ?_
  exact foldl_pair_keeps (fun A => EmbViewInv v₀ g A.1.seenCopy A.2) _ qs
    (⟨∅, ∅, ∅, [], [], [], ∅, []⟩, v₀) (fun A q hq hA => p4WVStep_viewInv P S6 mem₀ OS v₀ g q (hT q hq) A hA)
    (EmbViewInv.start v₀ g)

/-- **The entering edges** get the walk `[(e, true)]`: when `g` asks for it there, the invariant
holds after them with these edges added to the written ones. -/
theorem EmbViewInv.insSelf {v₀ : EmbView} {g : Embedding} {W : Finset ℕ} {v : EmbView}
    (h : EmbViewInv v₀ g W v) {L : List ℕ} (hL : ∀ e ∈ L, g e = [(e, true)]) :
    EmbViewInv v₀ g (W ∪ L.toFinset) (v.apply (insSelfChange L)) := by
  classical
  have hfst : (insSelfChange L).map Prod.fst = L := by
    unfold insSelfChange
    clear hL
    induction L with
    | nil => rfl
    | cons e L ih => simp only [List.map_cons, ih]
  refine h.apply (fun x hx => ?_) (fun e he => ?_) Finset.subset_union_left (fun e he => ?_)
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact (hL e he).symm
  · rw [hfst]
    rcases Finset.mem_union.mp he with h' | h'
    · exact Or.inl h'
    · exact Or.inr (List.mem_toFinset.mp h')
  · rw [hfst] at he
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr he)

/-! ## The seen edges at the end -/

/-- A task grows the seen set. -/
theorem p4WVStep_seen_mono (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) (OS : Finset ℕ) (A : Phase4WS × EmbView) (q : SpanUpdTask × P4TaskOut) :
    A.1.seenCopy ⊆ (p4WVStep P S6 mem₀ OS A q).1.seenCopy := by
  rcases p4WVStep_cases P S6 mem₀ OS A q with h | ⟨hs, d, hd, hb, h⟩
  · rw [h]
  · rw [h]; exact (p4TaskWS_facts _ _ _ _ _ _ _).1.2.2.1

/-- A new slot grows the seen set. -/
theorem p4NewStep_seen_mono (P : DSParams) {cap : ℕ} (S' : BucketSpannerState cap)
    (A : Phase4WS × EmbView) (q : ℕ × List ℕ) :
    A.1.seenCopy ⊆ (p4NewStep P S' A q).1.seenCopy := by
  rcases p4NewStep_cases P S' A q with h | ⟨hs, d, hd, h⟩
  · rw [h]
  · rw [h]; exact (p4NewScan_facts _ _ _).1.2.2.1

/-- **The scans of a task see** each edge of `R` in the new graph and outside the new spanner,
and each edge that `U_H` deletes when it is in the new graph, outside the new spanner, and in the
old output graph `OS`. -/
theorem p4TaskWS_seen_of (P : DSParams) (d : DSHist) (OS : Finset ℕ) (UH : List Update)
    (D R : List ℕ) (S : Phase4WS) {e : ℕ} (hG : e ∈ (d.state P).G.E) (hH : e ∉ (d.state P).H.E)
    (he : e ∈ R ∨ (Update.delete e ∈ UH ∧ e ∈ OS)) :
    e ∈ (p4TaskWS P d OS UH D R S).seenCopy := by
  classical
  have hW : P4Grows (p4TaskScan P d OS UH D R S) (p4TaskWS P d OS UH D R S) :=
    foldl_grows _ _ (fun T x _ => p4Grows_stepDleft _ _ _ _ T x) _
  refine hW.2.2.1 ?_
  rcases he with hR | ⟨hU, hO⟩
  · refine foldl_adds _ R (fun T x _ => p4Grows_stepR _ _ _ T x)
      (fun a T => a ∈ (d.state P).G.E → a ∉ (d.state P).H.E → a ∈ T.seenCopy)
      (fun a T T' hg h h1 h2 => hg.2.2.1 (h h1 h2)) (fun T a _ h1 h2 => ?_) _ e hR hG hH
    have hS' : p4StepR (d.state P).G.E (d.state P).H.E true T a =
        pushCopy { T with reemb := pushDedup T.reemb a } a := by
      simp only [p4StepR, h1, h2, not_false_eq_true, and_self, ↓reduceIte]
    rw [hS']
    exact mem_pushCopy_seenCopy _ a
  · have hU' := foldl_adds _ UH (fun T u _ => p4Grows_stepUH (d.state P).G.E (d.state P).H.E OS
      true T u) (fun u T => ∀ x, u = Update.delete x → x ∈ (d.state P).G.E →
        x ∉ (d.state P).H.E → x ∈ OS → x ∈ T.seenCopy)
      (fun u T T' hg h x hx h1 h2 h3 => hg.2.2.1 (h x hx h1 h2 h3)) (fun T u _ x hx h1 h2 h3 => by
        subst hx
        have hS' : p4StepUH (d.state P).G.E (d.state P).H.E OS true T (Update.delete x) =
            pushCopy (p4StepEdge (d.state P).G.E (d.state P).H.E false true false false T x) x := by
          simp only [p4StepUH, Bool.true_and, h1, h2, not_false_eq_true, h3,
            and_self, decide_true]
          exact p4StepEdge_true _ _ _ _ _ _ _
        rw [hS']
        exact mem_pushCopy_seenCopy _ x) { S with copyBuf := [] } (Update.delete e) hU e rfl hG hH hO
    have hD : P4Grows (UH.foldl (p4StepUH (d.state P).G.E (d.state P).H.E OS true)
        { S with copyBuf := [] })
        (D.foldl (p4StepD (d.state P).G.E (d.state P).H.E)
          (UH.foldl (p4StepUH (d.state P).G.E (d.state P).H.E OS true) { S with copyBuf := [] })) :=
      foldl_grows _ _ (fun T x _ => p4Grows_stepD _ _ T x) _
    have hR' := foldl_grows (p4StepR (d.state P).G.E (d.state P).H.E true) R
      (fun T x _ => p4Grows_stepR _ _ _ T x)
      (D.foldl (p4StepD (d.state P).G.E (d.state P).H.E)
          (UH.foldl (p4StepUH (d.state P).G.E (d.state P).H.E OS true) { S with copyBuf := [] }))
    exact hR'.2.2.1 (hD.2.2.1 hU')

/-- **A new slot sees** each edge of its list outside its spanner. -/
theorem p4NewScan_seen_of (HE : Finset ℕ) (l : List ℕ) (S : Phase4WS) {e : ℕ} (hl : e ∈ l)
    (hH : e ∉ HE) : e ∈ (l.foldl (p4StepNew HE) { S with copyBuf := [] }).seenCopy := by
  classical
  refine foldl_adds _ l (fun T x _ => p4Grows_stepNew HE T x) (fun a T => a ∉ HE → a ∈ T.seenCopy)
    (fun a T T' hg h h1 => hg.2.2.1 (h h1)) (fun T a _ h1 => ?_) _ e hl hH
  have hS' : ∀ T' : Phase4WS, (if a ∉ HE then pushCopy T' a else T') = pushCopy T' a :=
    fun T' => ite_eq_left_iff.mpr (fun h' => absurd h1 h')
  unfold p4StepNew
  rw [hS']
  exact mem_pushCopy_seenCopy _ a

/-- **The tasks see their edges**: at the end of the tasks and the new slots, the seen set holds
the edges that `p4TaskWS_seen_of` gives for each task that updates its slot. -/
theorem p4SpanWV_seen_task (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) (OS : Finset ℕ) (v₀ : EmbView) (qs : List (SpanUpdTask × P4TaskOut))
    (ns : List (ℕ × List ℕ)) {q : SpanUpdTask × P4TaskOut} (hq : q ∈ qs) (hs : q.1.slot < cap)
    {d : DSHist} (hd : S6 ⟨q.1.slot, hs⟩ = some d) (hb : mem₀ q.1.batchPtr ≠ 0) {e : ℕ}
    (hG : e ∈ ((p4NewHist P mem₀ d q.1).state P).G.E)
    (hH : e ∉ ((p4NewHist P mem₀ d q.1).state P).H.E)
    (he : e ∈ q.2.rL ∨ (Update.delete e ∈ q.2.UH ∧ e ∈ OS)) :
    e ∈ (p4SpanWV P S6 mem₀ OS v₀ (qs.map Prod.fst) qs ns).1.seenCopy := by
  unfold p4SpanWV
  refine foldl_set_mono (fun A : Phase4WS × EmbView => A.1.seenCopy) _
    (fun A q' => p4NewStep_seen_mono P _ A q') ns _ ?_
  refine foldl_set_mem (fun A : Phase4WS × EmbView => A.1.seenCopy) _
    (fun A q' => p4WVStep_seen_mono P S6 mem₀ OS A q') (a₀ := q) (fun A => ?_) qs _ hq
  rw [p4WVStep, p4OnTask_of hs hd hb]
  exact p4TaskWS_seen_of P _ OS _ _ _ A.1 hG hH he

/-- **The new slots see their edges**: at the end, the seen set holds each edge of the list of a
new slot outside the spanner of the slot. -/
theorem p4SpanWV_seen_new (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) (OS : Finset ℕ) (v₀ : EmbView) (qs : List (SpanUpdTask × P4TaskOut))
    (ns : List (ℕ × List ℕ)) {q : ℕ × List ℕ} (hq : q ∈ ns) (hs : q.1 < cap) {d : DSHist}
    (hd : p4SpanAfter P S6 mem₀ (qs.map Prod.fst) ⟨q.1, hs⟩ = some d) {e : ℕ} (he : e ∈ q.2)
    (hH : e ∉ (d.state P).H.E) :
    e ∈ (p4SpanWV P S6 mem₀ OS v₀ (qs.map Prod.fst) qs ns).1.seenCopy := by
  unfold p4SpanWV
  refine foldl_set_mem (fun A : Phase4WS × EmbView => A.1.seenCopy) _
    (fun A q' => p4NewStep_seen_mono P _ A q') (a₀ := q) (fun A => ?_) ns _ hq
  simp only [p4NewStep, hs, ↓reduceDIte, hd]
  exact p4NewScan_seen_of _ q.2 A.1 he hH

end

end MinCostFlow.SparseCore.Program
