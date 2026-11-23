module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4WSFacts
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4NewLoop

/-!
# What one slot of Phase 4 does to the workspace (`AssemblyFirstStepP4TaskFacts`)

A task of Phase 4 changes the workspace by `p4TaskWS` (the scans of `U_H`, `D` and `R` of the
update of its slot, then the scan of the walks of the copied edges), and a new slot changes it by
the scan of the edge list of its graph (`p4NewStep`). This file collects what these do, from the
step facts of `AssemblyFirstStepP4WSFacts.lean`:

* `p4TaskWS_facts`: the workspace grows; the edges of `D` go into `inDtot`, `delSup` and
  `insSup`; the edges deleted and inserted by `U_H` go into `delSup` and `insSup`; the edges of
  `R` go into `reemb`; every such edge of the slot's graph is marked. A deleted edge of the old
  output graph that is in the slot's graph and not in its spanner, and that no earlier slot saw,
  gets its walk scanned, so the walk's edges go into `inDtot`, `delSup` and `insSup`. The set
  `inDtot` gains only the edges of `D` and of these walks, and the seen set gains only edges of
  the slot's graph.
* `p4MarkOK_taskWS`, `p4MarkOK_newScan`: the marks stay right.
* `p4WVStep_cases`, `p4NewStep_cases`: a task or a new slot either leaves the workspace or acts as
  above.
-/

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.SparseCore MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Read

public section

theorem pushCopy_seenCopy_sub (S : Phase4WS) (e : ℕ) :
    (pushCopy S e).seenCopy ⊆ insert e S.seenCopy := by
  classical
  unfold pushCopy
  split_ifs
  · exact Finset.subset_insert _ _
  · exact subset_rfl

theorem p4StepEdge_seenCopy_sub (GE HE : Finset ℕ) (fD fDel fIns fCopy : Bool) (S : Phase4WS)
    (e : ℕ) : (p4StepEdge GE HE fD fDel fIns fCopy S e).seenCopy ⊆
      if fCopy = true then insert e S.seenCopy else S.seenCopy := by
  have h7 := (p4StepEdge_false_fields GE HE fD fDel fIns S e).2.2.2.2.2.2.1
  cases fCopy with
  | false => exact h7 ▸ subset_rfl
  | true =>
    rw [p4StepEdge_true]
    refine (pushCopy_seenCopy_sub _ e).trans ?_
    rw [h7]; exact subset_rfl

/-- The seen set of a step of a task gains only edges of the slot's graph `GE`. -/
theorem p4StepUH_seenCopy_sub (GE HE OS : Finset ℕ) (isOld : Bool) (S : Phase4WS)
    (u : Update) : (p4StepUH GE HE OS isOld S u).seenCopy ⊆ S.seenCopy ∪ GE := by
  classical
  cases u with
  | insert e a b =>
    exact (p4StepEdge_seenCopy_sub _ _ _ _ _ _ S e).trans (by simp)
  | delete e =>
    refine (p4StepEdge_seenCopy_sub _ _ _ _ _ _ S e).trans ?_
    by_cases h : (isOld && decide (e ∈ GE ∧ e ∉ HE ∧ e ∈ OS)) = true
    · rw [if_pos h]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact Finset.insert_subset (Finset.mem_union_right _ h.2.1) Finset.subset_union_left
    · rw [if_neg h]; exact Finset.subset_union_left
  | split a b c d => exact Finset.subset_union_left

theorem p4StepR_seenCopy_sub (GE HE : Finset ℕ) (isOld : Bool) (S : Phase4WS) (e : ℕ) :
    (p4StepR GE HE isOld S e).seenCopy ⊆ S.seenCopy ∪ GE := by
  classical
  have hS' : p4StepR GE HE isOld S e = if isOld = true ∧ e ∈ GE ∧ e ∉ HE then
      pushCopy { S with reemb := pushDedup S.reemb e } e
      else { S with reemb := pushDedup S.reemb e } := rfl
  rw [hS']
  split_ifs with h
  · exact (pushCopy_seenCopy_sub _ e).trans
      (Finset.insert_subset (Finset.mem_union_right _ h.2.1) Finset.subset_union_left)
  · exact Finset.subset_union_left

/-- A fold keeps a property `Q` when each step keeps it. -/
private theorem foldl_keeps' {α : Type} (Q : Phase4WS → Prop) (f : Phase4WS → α → Phase4WS)
    (l : List α) (hf : ∀ S a, Q S → Q (f S a)) (S : Phase4WS) (hS : Q S) : Q (l.foldl f S) :=
  foldl_keeps Q f hf l S hS

set_option maxHeartbeats 800000 in
/-- **What a task does to the workspace.** See the module docstring. -/
theorem p4TaskWS_facts (P : DSParams) (d : DSHist) (OS : Finset ℕ) (UH : List Update)
    (D R : List ℕ) (S : Phase4WS) :
    P4Grows S (p4TaskWS P d OS UH D R S) ∧
    (∀ e ∈ D, e ∈ (p4TaskWS P d OS UH D R S).inDtot ∧ e ∈ (p4TaskWS P d OS UH D R S).delSup ∧
      e ∈ (p4TaskWS P d OS UH D R S).insSup ∧
      (e ∈ (d.state P).G.E → e ∈ (p4TaskWS P d OS UH D R S).inAct)) ∧
    (∀ e ∈ uhDelFinset UH, e ∈ (p4TaskWS P d OS UH D R S).delSup ∧
      (e ∈ (d.state P).G.E → e ∈ (p4TaskWS P d OS UH D R S).inAct)) ∧
    (∀ e ∈ uhInsFinset UH, e ∈ (p4TaskWS P d OS UH D R S).insSup ∧
      (e ∈ (d.state P).G.E → e ∈ (p4TaskWS P d OS UH D R S).inAct)) ∧
    (∀ e ∈ R, e ∈ (p4TaskWS P d OS UH D R S).reemb) ∧
    (∀ e ∈ uhDelFinset UH, e ∈ (d.state P).G.E → e ∉ (d.state P).H.E → e ∈ OS →
      e ∉ S.seenCopy → ∀ x ∈ walkEdges (piTotal (d.state P) e),
        x ∈ (p4TaskWS P d OS UH D R S).inDtot ∧ x ∈ (p4TaskWS P d OS UH D R S).delSup ∧
        x ∈ (p4TaskWS P d OS UH D R S).insSup ∧
        (x ∈ (d.state P).G.E → x ∈ (p4TaskWS P d OS UH D R S).inAct)) ∧
    (p4TaskWS P d OS UH D R S).inDtot ⊆ S.inDtot ∪ D.toFinset ∪
      ((((d.state P).G.E \ (d.state P).H.E) ∩ OS).biUnion fun e =>
        walkEdges (piTotal (d.state P) e)) ∧
    (p4TaskWS P d OS UH D R S).seenCopy ⊆ S.seenCopy ∪ (d.state P).G.E := by
  classical
  set GE := (d.state P).G.E with hGE
  set HE := (d.state P).H.E with hHE
  set walk := piTotal (d.state P) with hwalk
  set S₀ : Phase4WS := { S with copyBuf := [] } with hS₀
  set S₁ := UH.foldl (p4StepUH GE HE OS true) S₀ with hS₁
  set S₂ := D.foldl (p4StepD GE HE) S₁ with hS₂
  set S₃ := R.foldl (p4StepR GE HE true) S₂ with hS₃
  have hscan : p4TaskScan P d OS UH D R S = S₃ := rfl
  set S₄ := S₃.copyBuf.foldl (p4StepDleft GE HE OS walk) S₃ with hS₄
  have hws : p4TaskWS P d OS UH D R S = S₄ := rfl
  rw [hws]
  -- Growth along the parts.
  have g₀ : P4Grows S S₀ := p4Grows_resetCopy S
  have g₁ : P4Grows S₀ S₁ := foldl_grows _ _ (fun T u _ => p4Grows_stepUH GE HE OS true T u) _
  have g₂ : P4Grows S₁ S₂ := foldl_grows _ _ (fun T e _ => p4Grows_stepD GE HE T e) _
  have g₃ : P4Grows S₂ S₃ := foldl_grows _ _ (fun T e _ => p4Grows_stepR GE HE true T e) _
  have g₄ : P4Grows S₃ S₄ :=
    foldl_grows _ _ (fun T e _ => p4Grows_stepDleft GE HE OS walk T e) _
  -- The edges of `U_H`.
  have hUH : ∀ u ∈ UH, (∀ e, u = .delete e → e ∈ S₁.delSup ∧ (e ∈ GE → e ∈ S₁.inAct)) ∧
      (∀ e a b, u = .insert e a b → e ∈ S₁.insSup ∧ (e ∈ GE → e ∈ S₁.inAct)) :=
    foldl_adds _ _ (fun T u _ => p4Grows_stepUH GE HE OS true T u)
      (fun u T => (∀ e, u = .delete e → e ∈ T.delSup ∧ (e ∈ GE → e ∈ T.inAct)) ∧
        (∀ e a b, u = .insert e a b → e ∈ T.insSup ∧ (e ∈ GE → e ∈ T.inAct)))
      (fun u T T' hg h => ⟨fun e hu => ⟨hg.2.2.2.1 e (h.1 e hu).1,
          fun he => hg.2.1 ((h.1 e hu).2 he)⟩,
        fun e a b hu => ⟨hg.2.2.2.2.1 e (h.2 e a b hu).1, fun he => hg.2.1 ((h.2 e a b hu).2 he)⟩⟩)
      (fun T u _ => p4StepUH_adds) S₀
  -- The edges of `D`.
  have hD : ∀ e ∈ D, e ∈ S₂.inDtot ∧ e ∈ S₂.delSup ∧ e ∈ S₂.insSup ∧ (e ∈ GE → e ∈ S₂.inAct) :=
    foldl_adds _ _ (fun T e _ => p4Grows_stepD GE HE T e)
      (fun e T => e ∈ T.inDtot ∧ e ∈ T.delSup ∧ e ∈ T.insSup ∧ (e ∈ GE → e ∈ T.inAct))
      (fun e T T' hg h => ⟨hg.1 h.1, hg.2.2.2.1 e h.2.1, hg.2.2.2.2.1 e h.2.2.1,
        fun he => hg.2.1 (h.2.2.2 he)⟩)
      (fun T e _ => by
        obtain ⟨h1, h2, h3, h4⟩ := p4StepD_adds (GE := GE) (HE := HE) (S := T) (e := e)
        exact ⟨h1, h3, h4, h2⟩) S₁
  -- The edges of `R`.
  have hR : ∀ e ∈ R, e ∈ S₃.reemb :=
    foldl_adds _ _ (fun T e _ => p4Grows_stepR GE HE true T e) (fun e T => e ∈ T.reemb)
      (fun e T T' hg h => hg.2.2.2.2.2 e h) (fun T e _ => p4StepR_adds) S₂
  have g₂₄ : P4Grows S₂ S₄ := g₃.trans g₄
  have g₁₄ : P4Grows S₁ S₄ := g₂.trans g₂₄
  -- The copied edges.
  have hcopy₁ : ∀ e ∈ uhDelFinset UH, e ∈ GE → e ∉ HE → e ∈ OS → e ∉ S.seenCopy →
      e ∈ S₁.copyBuf := by
    intro e he hG hH hO hseen
    have hmem : Update.delete e ∈ UH := by
      unfold uhDelFinset at he
      obtain ⟨u, hu, hue⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp he)
      cases u <;> simp at hue
      subst hue; exact hu
    have key := foldl_copies (p4StepUH GE HE OS true) (fun u => copyStep_stepUH GE HE OS true u)
      S₀ (fun u => u = .delete e) (fun _ => e) (fun T u hu hT => by
        subst hu
        have hp : p4StepUH GE HE OS true T (.delete e) =
            pushCopy (p4StepEdge GE HE false true false false T e) e := by
          have hc : (true && decide (e ∈ GE ∧ e ∉ HE ∧ e ∈ OS)) = true := by simp [hG, hH, hO]
          show p4StepEdge GE HE false true false (true && decide (e ∈ GE ∧ e ∉ HE ∧ e ∈ OS)) T e = _
          rw [hc, p4StepEdge_true]
        rw [hp]
        have h0 : CopyInv S₀ (p4StepEdge GE HE false true false false T e) := by
          obtain ⟨-, -, -, -, -, -, h7, h8⟩ := p4StepEdge_false_fields GE HE false true false T e
          intro x hx; rw [h7] at hx; rw [h8]; exact hT x hx
        exact (copyInv_pushCopy h0 e).2.2)
      UH S₀ (fun x hx => Or.inl hx) _ hmem rfl
    rcases key with h | h
    · exact absurd h hseen
    · exact h
  have hcopy₃ : ∀ e ∈ uhDelFinset UH, e ∈ GE → e ∉ HE → e ∈ OS → e ∉ S.seenCopy →
      e ∈ S₃.copyBuf := by
    intro e he hG hH hO hseen
    have h1 := hcopy₁ e he hG hH hO hseen
    have hc₂ := copyStep_foldl (p4StepD GE HE) (fun e => copyStep_stepD GE HE e) D S₀ S₁
    have hc₁ := copyStep_foldl (p4StepUH GE HE OS true)
      (fun u => copyStep_stepUH GE HE OS true u) UH S₀ S₀ (fun x hx => Or.inl hx)
    have hc₃ := copyStep_foldl (p4StepR GE HE true) (fun e => copyStep_stepR GE HE true e) R
      S₀ S₂ (hc₂ hc₁.1).1
    exact hc₃.2 e ((hc₂ hc₁.1).2 e h1)
  -- The walks of the copied edges.
  have hwalks : ∀ e ∈ S₃.copyBuf, e ∈ OS → ∀ x ∈ walkEdges (walk e), x ∈ S₄.inDtot ∧
      (x ∈ GE → x ∈ S₄.inAct) ∧ x ∈ S₄.delSup ∧ x ∈ S₄.insSup :=
    foldl_adds _ _ (fun T e _ => p4Grows_stepDleft GE HE OS walk T e)
      (fun e T => e ∈ OS → ∀ x ∈ walkEdges (walk e), x ∈ T.inDtot ∧ (x ∈ GE → x ∈ T.inAct) ∧
        x ∈ T.delSup ∧ x ∈ T.insSup)
      (fun e T T' hg h he x hx => ⟨hg.1 (h he x hx).1, fun hxG => hg.2.1 ((h he x hx).2.1 hxG),
        hg.2.2.2.1 x (h he x hx).2.2.1, hg.2.2.2.2.1 x (h he x hx).2.2.2⟩)
      (fun T e _ he => p4StepDleft_adds he) S₃
  -- `inDtot` and the seen set.
  have hdt₁ : S₁.inDtot = S₀.inDtot :=
    foldl_keeps' (fun T => T.inDtot = S₀.inDtot) _ UH
      (fun T u h => by rw [p4StepUH_inDtot]; exact h) S₀ rfl
  have hdt₂ : S₂.inDtot ⊆ S₁.inDtot ∪ D.toFinset := by
    have key : ∀ (l : List ℕ) (T : Phase4WS), (l.foldl (p4StepD GE HE) T).inDtot ⊆
        T.inDtot ∪ l.toFinset := by
      intro l
      induction l with
      | nil => intro T; simp
      | cons x l ih =>
        intro T y hy
        rcases Finset.mem_union.mp (ih _ hy) with h | h
        · simp only [p4StepD, Finset.mem_insert] at h
          simp only [List.toFinset_cons, Finset.mem_union, Finset.mem_insert]; tauto
        · simp only [List.toFinset_cons, Finset.mem_union, Finset.mem_insert]; tauto
    exact key D S₁
  have hdt₃ : S₃.inDtot = S₂.inDtot :=
    foldl_keeps' (fun T => T.inDtot = S₂.inDtot) _ R
      (fun T e h => by rw [p4StepR_inDtot]; exact h) S₂ rfl
  have hcand : ∀ e ∈ S₃.copyBuf, e ∈ GE ∧ e ∉ HE := fun e he => by
    have := mem_p4TaskScan_copyBuf_cand (P := P) (d := d) (OS := OS) (UH := UH) (D := D)
      (R := R) (S := S) (x := e) (hscan ▸ he)
    exact ⟨this.2.1, this.2.2⟩
  have hdt₄ : S₄.inDtot ⊆ S₃.inDtot ∪
      (((GE \ HE) ∩ OS).biUnion fun e => walkEdges (walk e)) := by
    have key : ∀ (l : List ℕ), (∀ e ∈ l, e ∈ GE ∧ e ∉ HE) → ∀ T : Phase4WS,
        (l.foldl (p4StepDleft GE HE OS walk) T).inDtot ⊆ T.inDtot ∪
          (((GE \ HE) ∩ OS).biUnion fun e => walkEdges (walk e)) := by
      intro l
      induction l with
      | nil => intro _ T; exact Finset.subset_union_left
      | cons x l ih =>
        intro hl T y hy
        rcases Finset.mem_union.mp (ih (fun e he => hl e (List.mem_cons_of_mem _ he)) _ hy)
          with h | h
        · have h' := p4StepDleft_inDtot (GE := GE) (HE := HE) (OS := OS) (walk := walk)
            (S := T) (e := x) h
          rcases Finset.mem_union.mp h' with h'' | h''
          · exact Finset.mem_union_left _ h''
          · split_ifs at h'' with hxO
            · have hx := hl x List.mem_cons_self
              exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x,
                Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr hx, hxO⟩, h''⟩)
            · simp at h''
        · exact Finset.mem_union_right _ h
    exact key _ hcand S₃
  have hsc₁ : S₁.seenCopy ⊆ S.seenCopy ∪ GE :=
    foldl_keeps' (fun T => T.seenCopy ⊆ S.seenCopy ∪ GE) _ UH
      (fun T u h => (p4StepUH_seenCopy_sub GE HE OS true T u).trans
        (Finset.union_subset h Finset.subset_union_right)) S₀ Finset.subset_union_left
  have hsc₂ : S₂.seenCopy ⊆ S.seenCopy ∪ GE :=
    foldl_keeps' (fun T => T.seenCopy ⊆ S.seenCopy ∪ GE) _ D
      (fun T e h => by simpa [p4StepD] using h) S₁ hsc₁
  have hsc₃ : S₃.seenCopy ⊆ S.seenCopy ∪ GE :=
    foldl_keeps' (fun T => T.seenCopy ⊆ S.seenCopy ∪ GE) _ R
      (fun T e h => (p4StepR_seenCopy_sub GE HE true T e).trans
        (Finset.union_subset h Finset.subset_union_right)) S₂ hsc₂
  have hsc₄ : S₄.seenCopy ⊆ S.seenCopy ∪ GE := by
    refine foldl_keeps' (fun T => T.seenCopy ⊆ S.seenCopy ∪ GE) _ S₃.copyBuf
      (fun T e h => ?_) S₃ hsc₃
    unfold p4StepDleft
    split_ifs
    · refine foldl_keeps' (fun T' => T'.seenCopy ⊆ S.seenCopy ∪ GE) _ _ (fun T' x h' => ?_) T h
      exact (p4StepEdge_seenCopy_sub GE HE true true true false T' x).trans h'
    · exact h
  -- Putting the parts together.
  refine ⟨g₀.trans (g₁.trans g₁₄), fun e he => ?_, fun e he => ?_, fun e he => ?_,
    fun e he => g₄.2.2.2.2.2 e (hR e he), fun e he hG hH hO hseen x hx => ?_, ?_, hsc₄⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hD e he
    exact ⟨g₂₄.1 h1, g₂₄.2.2.2.1 e h2, g₂₄.2.2.2.2.1 e h3, fun hG => g₂₄.2.1 (h4 hG)⟩
  · have hmem : Update.delete e ∈ UH := by
      unfold uhDelFinset at he
      obtain ⟨u, hu, hue⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp he)
      cases u <;> simp at hue
      subst hue; exact hu
    obtain ⟨h1, h2⟩ := (hUH _ hmem).1 e rfl
    exact ⟨g₁₄.2.2.2.1 e h1, fun hG => g₁₄.2.1 (h2 hG)⟩
  · have hmem : ∃ a b, Update.insert e a b ∈ UH := by
      unfold uhInsFinset at he
      obtain ⟨u, hu, hue⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp he)
      cases u <;> simp at hue
      subst hue; exact ⟨_, _, hu⟩
    obtain ⟨a, b, hmem⟩ := hmem
    obtain ⟨h1, h2⟩ := (hUH _ hmem).2 e a b rfl
    exact ⟨g₁₄.2.2.2.2.1 e h1, fun hG => g₁₄.2.1 (h2 hG)⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hwalks e (hcopy₃ e he hG hH hO hseen) hO x hx
    exact ⟨h1, h3, h4, h2⟩
  · intro x hx
    rcases Finset.mem_union.mp (hdt₄ hx) with h | h
    · rw [hdt₃] at h
      rcases Finset.mem_union.mp (hdt₂ h) with h | h
      · rw [hdt₁] at h
        exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
    · exact Finset.mem_union_right _ h

/-- **The marks after a task** stay right when the slot fits `A` and `T`. -/
theorem p4MarkOK_taskWS {A T : Finset ℕ} (P : DSParams) (d : DSHist) (OS : Finset ℕ)
    (UH : List Update) (D R : List ℕ) {S : Phase4WS}
    (hfit : P4SlotFits A T (d.state P).G.E (d.state P).H.E) (hS : P4MarkOK A T S) :
    P4MarkOK A T (p4TaskWS P d OS UH D R S) := by
  have h₀ : P4MarkOK A T ({ S with copyBuf := [] } : Phase4WS) := hS
  have h₁ := foldl_keeps (P4MarkOK A T) _ (fun S' u h => p4MarkOK_stepUH (OS := OS)
    (isOld := true) hfit h u) UH _ h₀
  have h₂ := foldl_keeps (P4MarkOK A T) _ (fun S' e h => p4MarkOK_stepD hfit h e) D _ h₁
  have h₃ := foldl_keeps (P4MarkOK A T) _ (fun S' e h => p4MarkOK_stepR (GE := (d.state P).G.E)
    (HE := (d.state P).H.E) (isOld := true) h e) R _ h₂
  exact foldl_keeps (P4MarkOK A T) _ (fun S' e h => p4MarkOK_stepDleft (OS := OS)
    (walk := piTotal (d.state P)) hfit h e) _ _ h₃

/-- **What a new slot does to the workspace**: it grows, every edge of the list is marked and
goes into `insSup`, `inDtot` does not change, the seen set gains only edges of the list, and the
marks stay right when the slot fits `A` and `T` and the list holds edges of its graph. -/
theorem p4NewScan_facts (HE : Finset ℕ) (l : List ℕ) (S : Phase4WS) :
    P4Grows S (l.foldl (p4StepNew HE) { S with copyBuf := [] }) ∧
    (∀ e ∈ l, e ∈ (l.foldl (p4StepNew HE) { S with copyBuf := [] }).inAct ∧
      e ∈ (l.foldl (p4StepNew HE) { S with copyBuf := [] }).insSup) ∧
    (l.foldl (p4StepNew HE) { S with copyBuf := [] }).inDtot = S.inDtot ∧
    (l.foldl (p4StepNew HE) { S with copyBuf := [] }).seenCopy ⊆ S.seenCopy ∪ l.toFinset := by
  classical
  refine ⟨(p4Grows_resetCopy S).trans
      (foldl_grows _ _ (fun T e _ => p4Grows_stepNew HE T e) _),
    foldl_adds _ _ (fun T e _ => p4Grows_stepNew HE T e) (fun e T => e ∈ T.inAct ∧ e ∈ T.insSup)
      (fun e T T' hg h => ⟨hg.2.1 h.1, hg.2.2.2.2.1 e h.2⟩) (fun T e _ => p4StepNew_adds) _,
    foldl_keeps (fun T => T.inDtot = S.inDtot) _ (fun T e h => by rw [p4StepNew_inDtot]; exact h)
      l _ rfl, ?_⟩
  refine foldl_keeps_mem (fun T => T.seenCopy ⊆ S.seenCopy ∪ l.toFinset) _ l
    (fun T e he h => ?_) _ Finset.subset_union_left
  have hsub : (p4StepNew HE T e).seenCopy ⊆ insert e T.seenCopy := by
    by_cases h1 : e ∈ HE <;> by_cases h2 : e ∈ T.seenCopy <;>
      simp [p4StepNew, pushCopy, h1, h2, Finset.subset_insert]
  exact hsub.trans (Finset.insert_subset (Finset.mem_union_right _ (List.mem_toFinset.mpr he)) h)

theorem p4MarkOK_newScan {A T GE HE : Finset ℕ} (hfit : P4SlotFits A T GE HE) {l : List ℕ}
    (hl : ∀ e ∈ l, e ∈ GE) {S : Phase4WS} (hS : P4MarkOK A T S) :
    P4MarkOK A T (l.foldl (p4StepNew HE) { S with copyBuf := [] }) :=
  foldl_keeps_mem (P4MarkOK A T) _ l (fun S' e he h => p4MarkOK_stepNew hfit h (hl e he)) _ hS

/-- A task leaves the workspace, or acts by `p4TaskWS` on the new history of its slot. -/
theorem p4WVStep_cases (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap) (mem₀ : ℕ → ℕ)
    (OS : Finset ℕ) (A : Phase4WS × EmbView) (q : SpanUpdTask × P4TaskOut) :
    (p4WVStep P S6 mem₀ OS A q).1 = A.1 ∨
      ∃ (hs : q.1.slot < cap) (d : DSHist), S6 ⟨q.1.slot, hs⟩ = some d ∧
        mem₀ q.1.batchPtr ≠ 0 ∧
        (p4WVStep P S6 mem₀ OS A q).1 =
          p4TaskWS P (p4NewHist P mem₀ d q.1) OS q.2.UH q.2.dL q.2.rL A.1 := by
  by_cases hs : q.1.slot < cap
  · cases hd : S6 ⟨q.1.slot, hs⟩ with
    | none =>
      left
      simp only [p4WVStep, p4OnTask, hs, ↓reduceDIte, hd]
    | some d =>
      by_cases hb : mem₀ q.1.batchPtr = 0
      · left
        rw [p4WVStep, p4OnTask_empty hs hd hb]
      · right
        refine ⟨hs, d, hd, hb, ?_⟩
        rw [p4WVStep, p4OnTask_of hs hd hb]
  · left
    simp only [p4WVStep, p4OnTask, hs, ↓reduceDIte]

/-- A new slot leaves the workspace, or acts by the scan of its list. -/
theorem p4NewStep_cases (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (A : Phase4WS × EmbView) (q : ℕ × List ℕ) :
    (p4NewStep P S6 A q).1 = A.1 ∨
      ∃ (hs : q.1 < cap) (d : DSHist), S6 ⟨q.1, hs⟩ = some d ∧
        (p4NewStep P S6 A q).1 = q.2.foldl (p4StepNew (d.state P).H.E) { A.1 with copyBuf := [] } := by
  by_cases hs : q.1 < cap
  · cases hd : S6 ⟨q.1, hs⟩ with
    | none => left; simp only [p4NewStep, hs, ↓reduceDIte, hd]
    | some d => right; exact ⟨hs, d, hd, by simp only [p4NewStep, hs, ↓reduceDIte, hd]⟩
  · left; simp only [p4NewStep, hs, ↓reduceDIte]

end

end MinCostFlow.SparseCore.Program
