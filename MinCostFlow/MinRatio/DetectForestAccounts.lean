module

public import MinCostFlow.MinRatio.DetectLoopInvariant

/-!
# Detect accounts in the evaluated forest

The proof of Theorem 5.1 (pages 29–30) preserves flow and resets only
the reported edge's absolute account. We interpret the evaluated
forest values at the fixed-point precision and show that a complete
search, read and reset round preserves this interpretation.
-/

public section
namespace MinCostFlow.MinRatio
open Chain LinkCut

/-- Each live edge has its model flow and current residual in its corresponding slot. -/
@[expose] def DetectForestAccounts {cfg : Alg2Config} (model : Alg2State cfg) (P : ℕ)
    (slotOf : ℕ → ℕ) (reported : Finset ℕ) (tree : PathTreeState) (trees : List AuxTree) : Prop :=
  ∀ e ∈ model.extG.E, ∃ value : PathEdgeValue, ∃ account : ℤ,
    (slotOf e, some value) ∈ forestPairs pathPayload tree.splay trees ∧
    (value.originalFlow : ℝ) / (2 : ℝ)^P = model.flow e ∧
    (account : ℝ) / (2 : ℝ)^P = resetReported model.detectAccum reported e ∧
    value.detector = account - detectorThreshold P cfg.ε (model.extℓ e)

/-- The model pending test is exactly the tree-ready test for each
live edge, and the selected value also represents its Query flow. -/
theorem detectForestAccounts_point {cfg : Alg2Config} (model : Alg2State cfg)
    {tree : PathTreeState} {trees : List AuxTree} {free : List ℕ} {depth slotOf : ℕ → ℕ}
    {P e : ℕ} {reported : Finset ℕ}
    (hi : LctInvWith pathPayload tree trees free depth)
    (ha : DetectForestAccounts model P slotOf reported tree trees)
    (he : e ∈ model.extG.E) (hedge : isEdgeSlot tree.n (slotOf e))
    (heps : 0 < cfg.ε) (hl : 0 < model.extℓ e) :
    ∃ value : PathEdgeValue,
      ((lctExpose pathPayload tree (slotOf e)).splay.nodes (slotOf e)).val = some value ∧
      (value.originalFlow : ℝ) / (2 : ℝ)^P = model.flow e ∧
      (pathTreeReady tree (slotOf e) ↔ e ∈ (algorithm2_detect cfg model).1 \ reported) := by
  obtain ⟨value, account, hm, hf, hac, hd⟩ := ha e he
  have hv := pathTreeExpose_value_of_forestPair hi hm
  refine ⟨value, hv, hf, ?_⟩
  have hr : pathTreeReady tree (slotOf e) ↔ 0 ≤ value.detector := by
    constructor
    · rintro ⟨_, _, v, hv', hn⟩
      exact Option.some.inj (hv'.symm.trans hv) ▸ hn
    · intro hn
      exact (pathTreeReady_iff_forestPairs hi _).2 ⟨hedge, value, hm, hn⟩
  exact hr.trans (detect_residual_pending model he heps hl hac hd)

/-- Resetting the selected payload keeps every live edge's flow and
changes the interpreted detection account only for its reported name. -/
theorem detectForestAccounts_report {cfg : Alg2Config} (model : Alg2State cfg)
    {tree : PathTreeState} {trees : List AuxTree} {free : List ℕ} {depth slotOf : ℕ → ℕ}
    {P edge : ℕ} {reported : Finset ℕ} {prior : PathEdgeValue}
    (hi : LctInvWith pathPayload tree trees free depth)
    (ha : DetectForestAccounts model P slotOf reported tree trees)
    (he : edge ∈ model.extG.E) (hinj : Set.InjOn slotOf (model.extG.E : Set ℕ))
    (hs : slotOf edge ∈ trees.flatMap AuxTree.toList)
    (hflow : (prior.originalFlow : ℝ) / (2 : ℝ)^P = model.flow edge) :
    let slot := slotOf edge
    let read := lctExpose pathPayload (lctExpose pathPayload tree slot) slot
    let value := { prior with detector := -detectorThreshold P cfg.ε (model.extℓ edge) }
    let updated := pathTreeWrite read slot (some value)
    ∃ trees', LctInvWith pathPayload updated trees' free depth ∧
      DetectForestAccounts model P slotOf (insert edge reported) updated trees' := by
  dsimp only
  let value := { prior with detector := -detectorThreshold P cfg.ε (model.extℓ edge) }
  obtain ⟨trees', hInv, hpair⟩ := pathTreeReport_forestPairs hi hs (some value)
  refine ⟨trees', hInv, ?_⟩
  intro e hem
  by_cases h : e = edge
  · subst e
    have hnew := (hpair (slotOf edge) (some value)).2 (Or.inl ⟨rfl, rfl⟩)
    refine ⟨value, 0, hnew, hflow, ?_, ?_⟩
    · simp [resetReported]
    · simp [value]
  · obtain ⟨v, account, hv, hf, hn, hd⟩ := ha e hem
    have hne : slotOf e ≠ slotOf edge := fun eq => h (hinj hem he eq)
    exact ⟨v, account, (hpair _ _).2 (Or.inr ⟨hne, hv⟩), hf,
      by simpa [resetReported, h] using hn, hd⟩

/-- A ready slot names a pending edge and the reset preserves the
evaluated account invariant for the enlarged report. -/
theorem detectForestAccounts_ready_round {cfg : Alg2Config} (model : Alg2State cfg)
    {tree : PathTreeState} {trees : List AuxTree} {free : List ℕ} {depth slotOf : ℕ → ℕ}
    {P slot : ℕ} {reported : Finset ℕ}
    (hi : LctInvWith pathPayload tree trees free depth)
    (ha : DetectForestAccounts model P slotOf reported tree trees)
    (hinj : Set.InjOn slotOf (model.extG.E : Set ℕ))
    (hcover : ∀ x, pathTreeReady tree x →
      ∃ e ∈ model.extG.E, slotOf e = x)
    (heps : 0 < cfg.ε) (hl : ∀ e ∈ model.extG.E, 0 < model.extℓ e)
    (hr : pathTreeReady tree slot) :
    ∃ edge ∈ (algorithm2_detect cfg model).1 \ reported, slotOf edge = slot ∧
      ∃ prior : PathEdgeValue,
        ((lctExpose pathPayload tree slot).splay.nodes slot).val = some prior ∧
        let read := lctExpose pathPayload (lctExpose pathPayload tree slot) slot
        let value := { prior with detector := -detectorThreshold P cfg.ε (model.extℓ edge) }
        let updated := pathTreeWrite read slot (some value)
        ∃ trees', LctInvWith pathPayload updated trees' free depth ∧
          DetectForestAccounts model P slotOf (insert edge reported) updated trees' := by
  obtain ⟨hedge, value, hpair, _⟩ := (pathTreeReady_iff_forestPairs hi slot).mp hr
  have hactive := pathTree_forestPair_mem_active hpair
  obtain ⟨edge, he, hslot⟩ := hcover slot hr
  subst slot
  obtain ⟨prior, hprior, hflow, hpending⟩ :=
    detectForestAccounts_point model hi ha he hedge heps (hl edge he)
  exact ⟨edge, hpending.mp hr, rfl, prior, hprior,
    detectForestAccounts_report model hi ha he hinj hactive hflow⟩

/-- The ready branch extends the list represented in machine memory
and decreases the pending count by one. -/
theorem detectForestAccounts_ready_snoc {cfg : Alg2Config} (model : Alg2State cfg)
    {tree : PathTreeState} {trees : List AuxTree} {free : List ℕ} {depth slotOf : ℕ → ℕ}
    {P slot : ℕ} {reported : List ℕ}
    (hi : LctInvWith pathPayload tree trees free depth)
    (ha : DetectForestAccounts model P slotOf reported.toFinset tree trees)
    (hinj : Set.InjOn slotOf (model.extG.E : Set ℕ))
    (hcover : ∀ x, pathTreeReady tree x →
      ∃ e ∈ model.extG.E, slotOf e = x)
    (heps : 0 < cfg.ε) (hl : ∀ e ∈ model.extG.E, 0 < model.extℓ e)
    (hn : reported.Nodup) (hs : reported.toFinset ⊆ (algorithm2_detect cfg model).1)
    (hr : pathTreeReady tree slot) :
    ∃ edge ∈ model.extG.E, slotOf edge = slot ∧
      (reported ++ [edge]).Nodup ∧
      (reported ++ [edge]).toFinset ⊆ (algorithm2_detect cfg model).1 ∧
      ((algorithm2_detect cfg model).1 \ (reported ++ [edge]).toFinset).card + 1 =
        ((algorithm2_detect cfg model).1 \ reported.toFinset).card ∧
      ∃ prior : PathEdgeValue,
        ((lctExpose pathPayload tree slot).splay.nodes slot).val = some prior ∧
        let read := lctExpose pathPayload (lctExpose pathPayload tree slot) slot
        let value := { prior with detector := -detectorThreshold P cfg.ε (model.extℓ edge) }
        let updated := pathTreeWrite read slot (some value)
        ∃ trees', LctInvWith pathPayload updated trees' free depth ∧
          DetectForestAccounts model P slotOf (reported ++ [edge]).toFinset updated trees' := by
  obtain ⟨edge, hpending, hslot, prior, hp, trees', hi', ha'⟩ :=
    detectForestAccounts_ready_round model hi ha hinj hcover heps hl hr
  obtain ⟨hn', hs', hc⟩ := detect_pending_snoc model hn hs hpending
  have hset : (reported ++ [edge]).toFinset = insert edge reported.toFinset := by
    ext e
    simp
  have he := (detect_ready_after_report model heps reported.toFinset edge).mpr hpending
  exact ⟨edge, he.1, hslot, hn', hs', hc, prior, hp, trees', hi', hset.symm ▸ ha'⟩

/-- A report preserves coverage of the slots that the next FindReady
call may return. The reset removes its selected slot from that set. -/
theorem detect_ready_coverage_after_report {tree : PathTreeState} {slot : ℕ}
    {E : Finset ℕ} {slotOf : ℕ → ℕ} (hr : pathTreeReady tree slot)
    (hcover : ∀ x, pathTreeReady tree x → ∃ e ∈ E, slotOf e = x)
    (value : PathEdgeValue) (hneg : value.detector < 0) :
    let read := lctExpose pathPayload (lctExpose pathPayload tree slot) slot
    ∀ x, pathTreeReady (pathTreeWrite read slot (some value)) x →
      ∃ e ∈ E, slotOf e = x := by
  intro read x hx
  exact hcover x ((pathTreeReady_after_report hr value hneg x).mp hx).2

/-- An exhausted search certifies that no live model account reaches
its threshold after the reported resets. -/
theorem detectForestAccounts_below_threshold {cfg : Alg2Config} (model : Alg2State cfg)
    {tree : PathTreeState} {trees : List AuxTree} {free : List ℕ} {depth slotOf : ℕ → ℕ}
    {P : ℕ} {reported : Finset ℕ}
    (hi : LctInvWith pathPayload tree trees free depth)
    (ha : DetectForestAccounts model P slotOf reported tree trees)
    (hedge : ∀ e ∈ model.extG.E, isEdgeSlot tree.n (slotOf e))
    (heps : 0 < cfg.ε) (hl : ∀ e ∈ model.extG.E, 0 < model.extℓ e)
    (hstop : ∀ slot, ¬ pathTreeReady tree slot) :
    ∀ e ∈ model.extG.E, ¬ cfg.ε ≤ model.extℓ e * resetReported model.detectAccum reported e := by
  intro e he hready
  obtain ⟨_, _, _, hpending⟩ :=
    detectForestAccounts_point model hi ha he (hedge e he) heps (hl e he)
  exact hstop (slotOf e) (hpending.mpr ((detect_ready_after_report model heps reported e).mp
    ⟨he, hready⟩))

/-- If FindReady is exhausted, the accumulated report is exactly the
model's report and the interpreted accounts equal the model's resets. -/
theorem detectForestAccounts_exhausted {cfg : Alg2Config} (model : Alg2State cfg)
    {tree : PathTreeState} {trees : List AuxTree} {free : List ℕ} {depth slotOf : ℕ → ℕ}
    {P : ℕ} {reported : Finset ℕ}
    (hi : LctInvWith pathPayload tree trees free depth)
    (ha : DetectForestAccounts model P slotOf reported tree trees)
    (hedge : ∀ e ∈ model.extG.E, isEdgeSlot tree.n (slotOf e))
    (heps : 0 < cfg.ε) (hl : ∀ e ∈ model.extG.E, 0 < model.extℓ e)
    (hsub : reported ⊆ (algorithm2_detect cfg model).1)
    (hstop : ∀ slot, ¬ pathTreeReady tree slot) :
    reported = (algorithm2_detect cfg model).1 ∧
      resetReported model.detectAccum reported = (algorithm2_detect cfg model).2.detectAccum :=
  detect_exhausted model heps hsub
    (detectForestAccounts_below_threshold model hi ha hedge heps hl hstop)

/-- After a complete report, the final forest represents the new model
state with an empty set of reports for the next call. -/
theorem detectForestAccounts_next {cfg : Alg2Config} (model : Alg2State cfg)
    {tree : PathTreeState} {trees : List AuxTree} {slotOf : ℕ → ℕ}
    {P : ℕ} {reported : Finset ℕ}
    (ha : DetectForestAccounts model P slotOf reported tree trees)
    (hreset : resetReported model.detectAccum reported = (algorithm2_detect cfg model).2.detectAccum) :
    DetectForestAccounts (algorithm2_detect cfg model).2 P slotOf ∅ tree trees := by
  intro e he
  have he' : e ∈ model.extG.E := by simpa [algorithm2_detect] using he
  obtain ⟨value, account, hp, hf, hac, hd⟩ := ha e he'
  refine ⟨value, account, hp, ?_, ?_, ?_⟩
  · simpa [algorithm2_detect] using hf
  · rw [congrFun hreset e] at hac
    simpa [resetReported] using hac
  · simpa [algorithm2_detect] using hd

end MinCostFlow.MinRatio
