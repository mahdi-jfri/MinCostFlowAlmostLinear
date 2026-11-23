module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4TaskDefs

/-!
# What the steps of Phase 4 do to the workspace (`AssemblyFirstStepP4WSFacts`)

The scans of Phase 4 change the workspace `Phase4WS` one edge at a time (`p4StepEdge`,
`p4StepUH`, `p4StepD`, `p4StepR`, `p4StepDleft`, `p4StepNew`). To show later that the candidate
lists of the workspace contain the sets of the model, this file proves three kinds of facts about
these steps, and about folds of them.

* **Growth** (`P4Grows`). No step removes anything from the flags `inDtot`, `inAct`, the seen
  set of the copy buffer, or the lists `delSup`, `insSup`, `reemb`. So what one step adds stays
  until the end (`foldl_adds`).
* **The marks** (`P4MarkOK A T`). A step of a slot with graph `GE` and spanner `HE` marks an edge
  `e ∈ GE` active and makes it a target edge exactly when `e ∈ HE`. When the graphs of the slots
  are apart, the active edges lie in the union `A` of the graphs, and an active edge is a target
  edge exactly when it lies in the union `T` of the spanners.
* **The copy buffer.** After the reset of the copy buffer at the start of a slot, an edge that the
  slot copies and that no earlier slot saw is in the copy buffer (`CopyInv`).
-/

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.SparseCore MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-! ## Growth -/

public section

/-- The workspace `S'` keeps everything of `S`: the flags `inDtot`, `inAct` and the seen set only
grow, and the candidate lists keep their entries. -/
@[expose] def P4Grows (S S' : Phase4WS) : Prop :=
  S.inDtot ⊆ S'.inDtot ∧ S.inAct ⊆ S'.inAct ∧ S.seenCopy ⊆ S'.seenCopy ∧
    (∀ e ∈ S.delSup, e ∈ S'.delSup) ∧ (∀ e ∈ S.insSup, e ∈ S'.insSup) ∧
    (∀ e ∈ S.reemb, e ∈ S'.reemb)

theorem P4Grows.refl (S : Phase4WS) : P4Grows S S :=
  ⟨subset_rfl, subset_rfl, subset_rfl, fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem P4Grows.trans {S₁ S₂ S₃ : Phase4WS} (h₁ : P4Grows S₁ S₂) (h₂ : P4Grows S₂ S₃) :
    P4Grows S₁ S₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
    fun e h => h₂.2.2.2.1 e (h₁.2.2.2.1 e h), fun e h => h₂.2.2.2.2.1 e (h₁.2.2.2.2.1 e h),
    fun e h => h₂.2.2.2.2.2 e (h₁.2.2.2.2.2 e h)⟩

/-- A fold of steps that grow grows. -/
theorem foldl_grows {α : Type} (f : Phase4WS → α → Phase4WS) (l : List α)
    (hf : ∀ S a, a ∈ l → P4Grows S (f S a)) (S : Phase4WS) : P4Grows S (l.foldl f S) := by
  induction l generalizing S with
  | nil => exact P4Grows.refl S
  | cons a l ih =>
    exact (hf S a List.mem_cons_self).trans
      (ih (fun T b hb => hf T b (List.mem_cons_of_mem a hb)) _)

/-- What each step of a fold adds for its own element stays until the end of the fold, when the
property `R` survives growth. -/
theorem foldl_adds {α : Type} (f : Phase4WS → α → Phase4WS) (l : List α)
    (hf : ∀ S a, a ∈ l → P4Grows S (f S a)) (R : α → Phase4WS → Prop)
    (hR : ∀ a S S', P4Grows S S' → R a S → R a S') (hadd : ∀ S a, a ∈ l → R a (f S a))
    (S : Phase4WS) : ∀ a ∈ l, R a (l.foldl f S) := by
  induction l generalizing S with
  | nil => intro a ha; cases ha
  | cons b l ih =>
    intro a ha
    rw [List.foldl_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hR _ _ _ (foldl_grows f l (fun T c hc => hf T c (List.mem_cons_of_mem _ hc)) _)
        (hadd S a List.mem_cons_self)
    · exact ih (fun T c hc => hf T c (List.mem_cons_of_mem _ hc))
        (fun T c hc => hadd T c (List.mem_cons_of_mem _ hc)) _ a ha

/-! ### The fields after one step -/

theorem pushCopy_fields (S : Phase4WS) (e : ℕ) :
    (pushCopy S e).inDtot = S.inDtot ∧ (pushCopy S e).inAct = S.inAct ∧
      (pushCopy S e).inTgt = S.inTgt ∧ (pushCopy S e).delSup = S.delSup ∧
      (pushCopy S e).insSup = S.insSup ∧ (pushCopy S e).reemb = S.reemb ∧
      S.seenCopy ⊆ (pushCopy S e).seenCopy := by
  classical
  unfold pushCopy
  split_ifs
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, subset_rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, Finset.subset_insert _ _⟩

theorem p4StepEdge_true (GE HE : Finset ℕ) (fD fDel fIns : Bool) (S : Phase4WS) (e : ℕ) :
    p4StepEdge GE HE fD fDel fIns true S e =
      pushCopy (p4StepEdge GE HE fD fDel fIns false S e) e := by
  simp only [p4StepEdge, Bool.false_eq_true, ↓reduceIte]

theorem p4StepEdge_false_fields (GE HE : Finset ℕ) (fD fDel fIns : Bool) (S : Phase4WS)
    (e : ℕ) :
    let S' := p4StepEdge GE HE fD fDel fIns false S e
    S'.inDtot = (if fD = true then insert e S.inDtot else S.inDtot) ∧
      S'.inAct = (p4Mark GE HE S e).inAct ∧ S'.inTgt = (p4Mark GE HE S e).inTgt ∧
      S'.delSup = (if fDel = true then pushDedup S.delSup e else S.delSup) ∧
      S'.insSup = (if fIns = true then pushDedup S.insSup e else S.insSup) ∧
      S'.reemb = S.reemb ∧ S'.seenCopy = S.seenCopy ∧ S'.copyBuf = S.copyBuf := by
  cases fD <;> cases fDel <;> cases fIns <;> simp [p4StepEdge, p4Mark]

theorem p4Mark_inAct_sub (GE HE : Finset ℕ) (S : Phase4WS) (e : ℕ) :
    S.inAct ⊆ (p4Mark GE HE S e).inAct := by
  classical
  simp only [p4Mark]
  split_ifs
  · exact Finset.subset_insert _ _
  · exact subset_rfl

theorem p4StepNew_fields (HE : Finset ℕ) (S : Phase4WS) (e : ℕ) :
    (p4StepNew HE S e).inDtot = S.inDtot ∧ (p4StepNew HE S e).inAct = insert e S.inAct ∧
      (p4StepNew HE S e).inTgt = (if e ∈ HE then insert e S.inTgt else S.inTgt.erase e) ∧
      (p4StepNew HE S e).delSup = S.delSup ∧
      (p4StepNew HE S e).insSup = pushDedup S.insSup e ∧ (p4StepNew HE S e).reemb = S.reemb ∧
      S.seenCopy ⊆ (p4StepNew HE S e).seenCopy := by
  classical
  by_cases h : e ∈ HE <;> by_cases h' : e ∈ S.seenCopy <;>
    simp [p4StepNew, pushCopy, h, h', Finset.subset_insert]

theorem p4StepR_fields (GE HE : Finset ℕ) (isOld : Bool) (S : Phase4WS) (e : ℕ) :
    let S' := p4StepR GE HE isOld S e
    S'.inDtot = S.inDtot ∧ S'.inAct = S.inAct ∧ S'.inTgt = S.inTgt ∧ S'.delSup = S.delSup ∧
      S'.insSup = S.insSup ∧ S'.reemb = pushDedup S.reemb e ∧ S.seenCopy ⊆ S'.seenCopy := by
  classical
  intro S'
  have hS' : S' = p4StepR GE HE isOld S e := rfl
  unfold p4StepR at hS'
  dsimp only at hS'
  split_ifs at hS'
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
      pushCopy_fields { S with reemb := pushDedup S.reemb e } e
    rw [hS']
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  · rw [hS']; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, subset_rfl⟩

/-! ### Growth of each step -/

theorem p4Grows_pushCopy (S : Phase4WS) (e : ℕ) : P4Grows S (pushCopy S e) := by
  obtain ⟨h1, h2, -, h4, h5, h6, h7⟩ := pushCopy_fields S e
  exact ⟨h1 ▸ subset_rfl, h2 ▸ subset_rfl, h7, fun x h => h4 ▸ h, fun x h => h5 ▸ h,
    fun x h => h6 ▸ h⟩

theorem p4Grows_stepEdge (GE HE : Finset ℕ) (fD fDel fIns fCopy : Bool) (S : Phase4WS) (e : ℕ) :
    P4Grows S (p4StepEdge GE HE fD fDel fIns fCopy S e) := by
  classical
  have h0 : P4Grows S (p4StepEdge GE HE fD fDel fIns false S e) := by
    obtain ⟨h1, h2, -, h4, h5, h6, h7, -⟩ := p4StepEdge_false_fields GE HE fD fDel fIns S e
    refine ⟨?_, h2 ▸ p4Mark_inAct_sub GE HE S e, h7 ▸ subset_rfl, fun x hx => ?_, fun x hx => ?_,
      fun x hx => h6 ▸ hx⟩
    · rw [h1]; split_ifs
      · exact Finset.subset_insert _ _
      · exact subset_rfl
    · rw [h4]; split_ifs
      · exact (mem_pushDedup_iff _ _ _).mpr (Or.inl hx)
      · exact hx
    · rw [h5]; split_ifs
      · exact (mem_pushDedup_iff _ _ _).mpr (Or.inl hx)
      · exact hx
  cases fCopy with
  | false => exact h0
  | true => rw [p4StepEdge_true]; exact h0.trans (p4Grows_pushCopy _ e)

theorem p4Grows_stepUH (GE HE OS : Finset ℕ) (isOld : Bool) (S : Phase4WS) (u : Update) :
    P4Grows S (p4StepUH GE HE OS isOld S u) := by
  cases u with
  | insert e a b => exact p4Grows_stepEdge _ _ _ _ _ _ S e
  | delete e => exact p4Grows_stepEdge _ _ _ _ _ _ S e
  | split a b c d => exact P4Grows.refl S

theorem p4Grows_stepD (GE HE : Finset ℕ) (S : Phase4WS) (e : ℕ) :
    P4Grows S (p4StepD GE HE S e) := by
  classical
  refine ⟨Finset.subset_insert _ _, ?_, subset_rfl,
    fun x h => (mem_pushDedup_iff _ _ _).mpr (Or.inl h),
    fun x h => (mem_pushDedup_iff _ _ _).mpr (Or.inl h), fun _ h => h⟩
  simp only [p4StepD]
  split_ifs
  · exact Finset.subset_insert _ _
  · exact subset_rfl

theorem p4Grows_stepR (GE HE : Finset ℕ) (isOld : Bool) (S : Phase4WS) (e : ℕ) :
    P4Grows S (p4StepR GE HE isOld S e) := by
  obtain ⟨h1, h2, -, h4, h5, h6, h7⟩ := p4StepR_fields GE HE isOld S e
  exact ⟨h1 ▸ subset_rfl, h2 ▸ subset_rfl, h7, fun x h => h4 ▸ h, fun x h => h5 ▸ h,
    fun x h => h6 ▸ (mem_pushDedup_iff _ _ _).mpr (Or.inl h)⟩

theorem p4Grows_stepDleft (GE HE OS : Finset ℕ) (walk : ℕ → List (ℕ × Bool)) (S : Phase4WS)
    (e : ℕ) : P4Grows S (p4StepDleft GE HE OS walk S e) := by
  classical
  unfold p4StepDleft
  split_ifs
  · exact foldl_grows _ _ (fun T x _ => p4Grows_stepEdge GE HE true true true false T x) S
  · exact P4Grows.refl S

theorem p4Grows_stepNew (HE : Finset ℕ) (S : Phase4WS) (e : ℕ) :
    P4Grows S (p4StepNew HE S e) := by
  obtain ⟨h1, h2, -, h4, h5, h6, h7⟩ := p4StepNew_fields HE S e
  exact ⟨h1 ▸ subset_rfl, h2 ▸ Finset.subset_insert _ _, h7, fun x h => h4 ▸ h,
    fun x h => h5 ▸ (mem_pushDedup_iff _ _ _).mpr (Or.inl h), fun x h => h6 ▸ h⟩

/-- Resetting the copy buffer grows the workspace. -/
theorem p4Grows_resetCopy (S : Phase4WS) : P4Grows S { S with copyBuf := [] } :=
  ⟨subset_rfl, subset_rfl, subset_rfl, fun _ h => h, fun _ h => h, fun _ h => h⟩

end

/-! ## What each step adds -/

public section

theorem p4StepEdge_adds {GE HE : Finset ℕ} {fD fDel fIns fCopy : Bool} {S : Phase4WS} {e : ℕ} :
    let S' := p4StepEdge GE HE fD fDel fIns fCopy S e
    (fD = true → e ∈ S'.inDtot) ∧ (e ∈ GE → e ∈ S'.inAct) ∧ (fDel = true → e ∈ S'.delSup) ∧
      (fIns = true → e ∈ S'.insSup) := by
  classical
  intro S'
  have h0 : let S0 := p4StepEdge GE HE fD fDel fIns false S e
      (fD = true → e ∈ S0.inDtot) ∧ (e ∈ GE → e ∈ S0.inAct) ∧ (fDel = true → e ∈ S0.delSup) ∧
        (fIns = true → e ∈ S0.insSup) := by
    obtain ⟨h1, h2, -, h4, h5, -⟩ := p4StepEdge_false_fields GE HE fD fDel fIns S e
    refine ⟨fun hf => ?_, fun hGE => ?_, fun hf => ?_, fun hf => ?_⟩
    · rw [h1, if_pos hf]; exact Finset.mem_insert_self _ _
    · rw [h2]; simp only [p4Mark, if_pos hGE]; exact Finset.mem_insert_self _ _
    · rw [h4, if_pos hf]; exact (mem_pushDedup_iff _ _ _).mpr (Or.inr rfl)
    · rw [h5, if_pos hf]; exact (mem_pushDedup_iff _ _ _).mpr (Or.inr rfl)
  cases fCopy with
  | false => exact h0
  | true =>
    have hg := p4Grows_pushCopy (p4StepEdge GE HE fD fDel fIns false S e) e
    have hS' : S' = pushCopy (p4StepEdge GE HE fD fDel fIns false S e) e :=
      p4StepEdge_true GE HE fD fDel fIns S e
    rw [hS']
    exact ⟨fun hf => hg.1 (h0.1 hf), fun hGE => hg.2.1 (h0.2.1 hGE),
      fun hf => hg.2.2.2.1 e (h0.2.2.1 hf), fun hf => hg.2.2.2.2.1 e (h0.2.2.2 hf)⟩

theorem p4StepD_adds {GE HE : Finset ℕ} {S : Phase4WS} {e : ℕ} :
    let S' := p4StepD GE HE S e
    e ∈ S'.inDtot ∧ (e ∈ GE → e ∈ S'.inAct) ∧ e ∈ S'.delSup ∧ e ∈ S'.insSup := by
  classical
  refine ⟨Finset.mem_insert_self _ _, fun hGE => ?_, (mem_pushDedup_iff _ _ _).mpr (Or.inr rfl),
    (mem_pushDedup_iff _ _ _).mpr (Or.inr rfl)⟩
  simp only [p4StepD, if_pos hGE]
  exact Finset.mem_insert_self _ _

theorem p4StepUH_adds {GE HE OS : Finset ℕ} {isOld : Bool} {S : Phase4WS} {u : Update} :
    let S' := p4StepUH GE HE OS isOld S u
    (∀ e, u = .delete e → e ∈ S'.delSup ∧ (e ∈ GE → e ∈ S'.inAct)) ∧
      (∀ e a b, u = .insert e a b → e ∈ S'.insSup ∧ (e ∈ GE → e ∈ S'.inAct)) := by
  intro S'
  refine ⟨fun e hu => ?_, fun e a b hu => ?_⟩
  · subst hu
    have h := p4StepEdge_adds (GE := GE) (HE := HE) (fD := false) (fDel := true) (fIns := false)
      (fCopy := isOld && decide (e ∈ GE ∧ e ∉ HE ∧ e ∈ OS)) (S := S) (e := e)
    exact ⟨h.2.2.1 rfl, h.2.1⟩
  · subst hu
    have h := p4StepEdge_adds (GE := GE) (HE := HE) (fD := false) (fDel := false) (fIns := true)
      (fCopy := false) (S := S) (e := e)
    exact ⟨h.2.2.2 rfl, h.2.1⟩

theorem p4StepR_adds {GE HE : Finset ℕ} {isOld : Bool} {S : Phase4WS} {e : ℕ} :
    e ∈ (p4StepR GE HE isOld S e).reemb := by
  rw [(p4StepR_fields GE HE isOld S e).2.2.2.2.2.1]
  exact (mem_pushDedup_iff _ _ _).mpr (Or.inr rfl)

theorem p4StepNew_adds {HE : Finset ℕ} {S : Phase4WS} {e : ℕ} :
    e ∈ (p4StepNew HE S e).inAct ∧ e ∈ (p4StepNew HE S e).insSup := by
  obtain ⟨-, h2, -, -, h5, -⟩ := p4StepNew_fields HE S e
  rw [h2, h5]
  exact ⟨Finset.mem_insert_self _ _, (mem_pushDedup_iff _ _ _).mpr (Or.inr rfl)⟩

/-- The scan of the walk of an edge `e` of the old output graph puts every edge of the walk into
`inDtot`, `delSup` and `insSup`, and marks those in `GE`. -/
theorem p4StepDleft_adds {GE HE OS : Finset ℕ} {walk : ℕ → List (ℕ × Bool)} {S : Phase4WS}
    {e : ℕ} (he : e ∈ OS) :
    ∀ x ∈ walkEdges (walk e), x ∈ (p4StepDleft GE HE OS walk S e).inDtot ∧
      (x ∈ GE → x ∈ (p4StepDleft GE HE OS walk S e).inAct) ∧
      x ∈ (p4StepDleft GE HE OS walk S e).delSup ∧ x ∈ (p4StepDleft GE HE OS walk S e).insSup := by
  classical
  intro x hx
  have hx' : x ∈ (walk e).map Prod.fst := List.mem_toFinset.mp hx
  unfold p4StepDleft
  rw [if_pos he]
  refine foldl_adds _ _ (fun T y _ => p4Grows_stepEdge GE HE true true true false T y)
    (fun y T => y ∈ T.inDtot ∧ (y ∈ GE → y ∈ T.inAct) ∧ y ∈ T.delSup ∧ y ∈ T.insSup)
    (fun y T T' hg h => ⟨hg.1 h.1, fun hy => hg.2.1 (h.2.1 hy), hg.2.2.2.1 y h.2.2.1,
      hg.2.2.2.2.1 y h.2.2.2⟩)
    (fun T y _ => ?_) S x hx'
  have h := p4StepEdge_adds (GE := GE) (HE := HE) (fD := true) (fDel := true) (fIns := true)
    (fCopy := false) (S := T) (e := y)
  exact ⟨h.1 rfl, h.2.1, h.2.2.1 rfl, h.2.2.2 rfl⟩

end

/-! ## The marks -/

public section

/-- The marks of the workspace agree with the sets `A` (edges of the graphs of the active slots)
and `T` (edges of their spanners): an active edge lies in `A`, and it is a target edge exactly when
it lies in `T`. -/
@[expose] def P4MarkOK (A T : Finset ℕ) (S : Phase4WS) : Prop :=
  S.inAct ⊆ A ∧ ∀ e ∈ S.inAct, (e ∈ S.inTgt ↔ e ∈ T)

/-- The graph `GE` and the spanner `HE` of a slot fit `A` and `T`. -/
@[expose] def P4SlotFits (A T GE HE : Finset ℕ) : Prop :=
  GE ⊆ A ∧ ∀ e ∈ GE, (e ∈ HE ↔ e ∈ T)

theorem p4MarkOK_congr {A T : Finset ℕ} {S S' : Phase4WS} (h1 : S'.inAct = S.inAct)
    (h2 : S'.inTgt = S.inTgt) (hS : P4MarkOK A T S) : P4MarkOK A T S' := by
  unfold P4MarkOK; rw [h1, h2]; exact hS

theorem p4MarkOK_mark {A T GE HE : Finset ℕ} (hfit : P4SlotFits A T GE HE) {S : Phase4WS}
    (hS : P4MarkOK A T S) (e : ℕ) : P4MarkOK A T (p4Mark GE HE S e) := by
  classical
  by_cases hGE : e ∈ GE
  · simp only [P4MarkOK, p4Mark, if_pos hGE]
    refine ⟨Finset.insert_subset (hfit.1 hGE) hS.1, fun x hx => ?_⟩
    by_cases hxe : x = e
    · subst hxe
      by_cases hHE : x ∈ HE
      · simp only [if_pos hHE, Finset.mem_insert_self, true_iff]; exact (hfit.2 x hGE).mp hHE
      · simp only [if_neg hHE, Finset.mem_erase, ne_eq, not_true_eq_false, false_and, false_iff]
        exact fun h => hHE ((hfit.2 x hGE).mpr h)
    · have hx' : x ∈ S.inAct := (Finset.mem_insert.mp hx).resolve_left hxe
      split_ifs
      · rw [Finset.mem_insert, or_iff_right hxe]; exact hS.2 x hx'
      · rw [Finset.mem_erase, and_iff_right hxe]; exact hS.2 x hx'
  · simp only [P4MarkOK, p4Mark, if_neg hGE]
    exact hS

theorem p4MarkOK_stepEdge {A T GE HE : Finset ℕ} (hfit : P4SlotFits A T GE HE)
    {fD fDel fIns fCopy : Bool} {S : Phase4WS} (hS : P4MarkOK A T S) (e : ℕ) :
    P4MarkOK A T (p4StepEdge GE HE fD fDel fIns fCopy S e) := by
  obtain ⟨-, h2, h3, -⟩ := p4StepEdge_false_fields GE HE fD fDel fIns S e
  have h0 := p4MarkOK_congr h2 h3 (p4MarkOK_mark hfit hS e)
  cases fCopy with
  | false => exact h0
  | true =>
    rw [p4StepEdge_true]
    exact p4MarkOK_congr (pushCopy_fields _ e).2.1 (pushCopy_fields _ e).2.2.1 h0

theorem p4MarkOK_stepUH {A T GE HE OS : Finset ℕ} (hfit : P4SlotFits A T GE HE) {isOld : Bool}
    {S : Phase4WS} (hS : P4MarkOK A T S) (u : Update) :
    P4MarkOK A T (p4StepUH GE HE OS isOld S u) := by
  cases u with
  | insert e a b => exact p4MarkOK_stepEdge hfit hS e
  | delete e => exact p4MarkOK_stepEdge hfit hS e
  | split a b c d => exact hS

theorem p4MarkOK_stepD {A T GE HE : Finset ℕ} (hfit : P4SlotFits A T GE HE) {S : Phase4WS}
    (hS : P4MarkOK A T S) (e : ℕ) : P4MarkOK A T (p4StepD GE HE S e) := by
  classical
  have h := p4MarkOK_mark hfit hS e
  simp only [P4MarkOK, p4Mark, p4StepD] at h ⊢
  exact h

theorem p4MarkOK_stepR {A T GE HE : Finset ℕ} {isOld : Bool} {S : Phase4WS}
    (hS : P4MarkOK A T S) (e : ℕ) : P4MarkOK A T (p4StepR GE HE isOld S e) :=
  p4MarkOK_congr (p4StepR_fields GE HE isOld S e).2.1 (p4StepR_fields GE HE isOld S e).2.2.1 hS

theorem p4MarkOK_stepDleft {A T GE HE OS : Finset ℕ} (hfit : P4SlotFits A T GE HE)
    {walk : ℕ → List (ℕ × Bool)} {S : Phase4WS} (hS : P4MarkOK A T S) (e : ℕ) :
    P4MarkOK A T (p4StepDleft GE HE OS walk S e) := by
  classical
  unfold p4StepDleft
  split_ifs
  · exact foldl_keeps (P4MarkOK A T) _ (fun S' x h => p4MarkOK_stepEdge hfit h x) _ _ hS
  · exact hS

/-- A step of a new slot marks an edge of its graph. -/
theorem p4MarkOK_stepNew {A T GE HE : Finset ℕ} (hfit : P4SlotFits A T GE HE) {S : Phase4WS}
    (hS : P4MarkOK A T S) {e : ℕ} (he : e ∈ GE) : P4MarkOK A T (p4StepNew HE S e) := by
  classical
  have h := p4MarkOK_mark hfit hS e
  obtain ⟨-, h2, h3, -⟩ := p4StepNew_fields HE S e
  refine p4MarkOK_congr (S := p4Mark GE HE S e) ?_ ?_ h
  · rw [h2]; simp only [p4Mark, if_pos he]
  · rw [h3]; simp only [p4Mark, if_pos he]

end

/-! ## Where `inDtot` grows -/

public section

theorem p4StepEdge_inDtot {GE HE : Finset ℕ} {fDel fIns fCopy : Bool} {S : Phase4WS} {e : ℕ}
    {fD : Bool} : (p4StepEdge GE HE fD fDel fIns fCopy S e).inDtot =
      if fD = true then insert e S.inDtot else S.inDtot := by
  have h1 := (p4StepEdge_false_fields GE HE fD fDel fIns S e).1
  cases fCopy with
  | false => exact h1
  | true => rw [p4StepEdge_true, (pushCopy_fields _ e).1, h1]

theorem p4StepUH_inDtot {GE HE OS : Finset ℕ} {isOld : Bool} {S : Phase4WS} {u : Update} :
    (p4StepUH GE HE OS isOld S u).inDtot = S.inDtot := by
  cases u with
  | insert e a b => exact p4StepEdge_inDtot
  | delete e => exact p4StepEdge_inDtot
  | split a b c d => rfl

theorem p4StepR_inDtot {GE HE : Finset ℕ} {isOld : Bool} {S : Phase4WS} {e : ℕ} :
    (p4StepR GE HE isOld S e).inDtot = S.inDtot :=
  (p4StepR_fields GE HE isOld S e).1

theorem p4StepNew_inDtot {HE : Finset ℕ} {S : Phase4WS} {e : ℕ} :
    (p4StepNew HE S e).inDtot = S.inDtot :=
  (p4StepNew_fields HE S e).1

theorem p4StepDleft_inDtot {GE HE OS : Finset ℕ} {walk : ℕ → List (ℕ × Bool)} {S : Phase4WS}
    {e : ℕ} : (p4StepDleft GE HE OS walk S e).inDtot ⊆
      S.inDtot ∪ (if e ∈ OS then walkEdges (walk e) else ∅) := by
  classical
  unfold p4StepDleft
  split_ifs with he
  · have key : ∀ (l : List ℕ) (T : Phase4WS),
        (l.foldl (p4StepEdge GE HE true true true false) T).inDtot ⊆ T.inDtot ∪ l.toFinset := by
      intro l
      induction l with
      | nil => intro T; simp
      | cons x l ih =>
        intro T
        refine (ih _).trans ?_
        intro y hy
        rw [p4StepEdge_inDtot] at hy
        simp only [↓reduceIte, Finset.mem_union, Finset.mem_insert] at hy
        simp only [List.toFinset_cons, Finset.mem_union, Finset.mem_insert]
        tauto
    exact key _ S
  · exact Finset.subset_union_left

end

/-! ## The copy buffer -/

public section

/-- Since the copy buffer of `S₀` was reset, every edge seen after `S₀` and not before is in the
copy buffer. -/
@[expose] def CopyInv (S₀ T : Phase4WS) : Prop :=
  ∀ x ∈ T.seenCopy, x ∈ S₀.seenCopy ∨ x ∈ T.copyBuf

theorem copyInv_pushCopy {S₀ T : Phase4WS} (h : CopyInv S₀ T) (e : ℕ) :
    CopyInv S₀ (pushCopy T e) ∧ (∀ x ∈ T.copyBuf, x ∈ (pushCopy T e).copyBuf) ∧
      (e ∈ S₀.seenCopy ∨ e ∈ (pushCopy T e).copyBuf) := by
  classical
  unfold pushCopy
  split_ifs with he
  · exact ⟨h, fun x hx => hx, h e he⟩
  · refine ⟨fun x hx => ?_, fun x hx => List.mem_append_left _ hx, Or.inr (by simp)⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Or.inr (by simp)
    · rcases h x hx with h' | h'
      · exact Or.inl h'
      · exact Or.inr (List.mem_append_left _ h')

/-- A step that copies only through `pushCopy` keeps `CopyInv` and the entries of the copy
buffer. -/
@[expose] def CopyStep (f : Phase4WS → Phase4WS) : Prop :=
  ∀ S₀ T, CopyInv S₀ T → CopyInv S₀ (f T) ∧ ∀ x ∈ T.copyBuf, x ∈ (f T).copyBuf

theorem copyStep_id : CopyStep id := fun _ _ h => ⟨h, fun _ hx => hx⟩

theorem copyStep_pushCopy (e : ℕ) : CopyStep fun T => pushCopy T e := fun _ _ h =>
  ⟨(copyInv_pushCopy h e).1, (copyInv_pushCopy h e).2.1⟩

theorem copyStep_stepEdge (GE HE : Finset ℕ) (fD fDel fIns fCopy : Bool) (e : ℕ) :
    CopyStep fun T => p4StepEdge GE HE fD fDel fIns fCopy T e := by
  intro S₀ T h
  dsimp only
  obtain ⟨-, -, -, -, -, -, h7, h8⟩ := p4StepEdge_false_fields GE HE fD fDel fIns T e
  have h0 : CopyInv S₀ (p4StepEdge GE HE fD fDel fIns false T e) := fun x hx => by
    rw [h7] at hx; rw [h8]; exact h x hx
  cases fCopy with
  | false => exact ⟨h0, fun x hx => h8 ▸ hx⟩
  | true =>
    rw [p4StepEdge_true]
    exact ⟨(copyInv_pushCopy h0 e).1, fun x hx => (copyInv_pushCopy h0 e).2.1 x (h8 ▸ hx)⟩

theorem copyStep_stepUH (GE HE OS : Finset ℕ) (isOld : Bool) (u : Update) :
    CopyStep fun T => p4StepUH GE HE OS isOld T u := by
  cases u with
  | insert e a b => exact copyStep_stepEdge _ _ _ _ _ _ e
  | delete e => exact copyStep_stepEdge _ _ _ _ _ _ e
  | split a b c d => exact copyStep_id

theorem copyStep_stepD (GE HE : Finset ℕ) (e : ℕ) : CopyStep fun T => p4StepD GE HE T e :=
  fun _ _ h => ⟨fun x hx => h x hx, fun _ hx => hx⟩

theorem copyStep_stepR (GE HE : Finset ℕ) (isOld : Bool) (e : ℕ) :
    CopyStep fun T => p4StepR GE HE isOld T e := by
  classical
  intro S₀ T h
  dsimp only
  have h1 : CopyInv S₀ { T with reemb := pushDedup T.reemb e } := fun x hx => h x hx
  have hS' : p4StepR GE HE isOld T e = if isOld = true ∧ e ∈ GE ∧ e ∉ HE then
      pushCopy { T with reemb := pushDedup T.reemb e } e
      else { T with reemb := pushDedup T.reemb e } := rfl
  rw [hS']
  split_ifs
  · exact ⟨(copyInv_pushCopy h1 e).1, fun x hx => (copyInv_pushCopy h1 e).2.1 x hx⟩
  · exact ⟨h1, fun _ hx => hx⟩

theorem copyStep_foldl {α : Type} (f : Phase4WS → α → Phase4WS)
    (hf : ∀ a, CopyStep fun T => f T a) (l : List α) : CopyStep fun T => l.foldl f T := by
  induction l with
  | nil => exact copyStep_id
  | cons a l ih =>
    intro S₀ T h
    obtain ⟨h1, h1'⟩ := hf a S₀ T h
    obtain ⟨h2, h2'⟩ := ih S₀ (f T a) h1
    exact ⟨h2, fun x hx => h2' x (h1' x hx)⟩

/-- In a fold of copy steps, an element whose step puts edge `g a` into the copy buffer (or sees
that `S₀` saw it) leaves `g a` in the copy buffer at the end, unless `S₀` saw it. -/
theorem foldl_copies {α : Type} (f : Phase4WS → α → Phase4WS)
    (hf : ∀ a, CopyStep fun T => f T a) (S₀ : Phase4WS) (Q : α → Prop) (g : α → ℕ)
    (hcopy : ∀ T a, Q a → CopyInv S₀ T → g a ∈ S₀.seenCopy ∨ g a ∈ (f T a).copyBuf) :
    ∀ (l : List α) (T : Phase4WS), CopyInv S₀ T → ∀ a ∈ l, Q a →
      g a ∈ S₀.seenCopy ∨ g a ∈ (l.foldl f T).copyBuf := by
  intro l
  induction l with
  | nil => intro T _ a ha; cases ha
  | cons b l ih =>
    intro T hT a ha hQ
    rw [List.foldl_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · rcases hcopy T a hQ hT with h | h
      · exact Or.inl h
      · exact Or.inr ((copyStep_foldl f hf l) S₀ (f T a) (hf a S₀ T hT).1 |>.2 _ h)
    · exact ih (f T b) (hf b S₀ T hT).1 a ha hQ

end

end MinCostFlow.SparseCore.Program
