module

public import MinCostFlow.MinRatio.DetectEmit
public import MinCostFlow.MinRatio.DetectProgress
public import MinCostFlow.MinRatio.DetectReset
public import MinCostFlow.MinRatio.PathTreeExpose

/-!
# Detect reporting invariant

In the proof of Theorem 5.1 (pages 29–30), Detect reports a ready
edge once and resets its account. A list of distinct names represents
the reports so far. Appending the name extends the set of reset
accounts, and an exhausted search gives the final output layout.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain IPM.Machine

/-- Appending a pending edge preserves the report invariant and
consumes exactly one pending report. -/
theorem detect_pending_snoc {cfg : Alg2Config} (st : Alg2State cfg)
    {edge : ℕ} {reported : List ℕ}
    (hnd : reported.Nodup) (hsub : reported.toFinset ⊆ (algorithm2_detect cfg st).1)
    (hpending : edge ∈ (algorithm2_detect cfg st).1 \ reported.toFinset) :
    (reported ++ [edge]).Nodup ∧
    (reported ++ [edge]).toFinset ⊆ (algorithm2_detect cfg st).1 ∧
    ((algorithm2_detect cfg st).1 \ (reported ++ [edge]).toFinset).card + 1 =
      ((algorithm2_detect cfg st).1 \ reported.toFinset).card := by
  obtain ⟨hmarked, hnew⟩ := Finset.mem_sdiff.mp hpending
  have hnd' : (reported ++ [edge]).Nodup := List.nodup_append.mpr
    ⟨hnd, List.nodup_singleton _, fun e he x hx heq => by
      have heq' : e = edge := heq.trans (List.mem_singleton.mp hx)
      exact hnew (List.mem_toFinset.mpr (heq' ▸ he))⟩
  have hsub' : (reported ++ [edge]).toFinset ⊆ (algorithm2_detect cfg st).1 := by
    rw [List.toFinset_append, List.toFinset_cons, List.toFinset_nil, LawfulSingleton.insert_empty_eq]
    exact Finset.union_subset hsub (Finset.singleton_subset_iff.mpr hmarked)
  refine ⟨hnd', hsub', ?_⟩
  rw [Finset.card_sdiff_of_subset hsub', Finset.card_sdiff_of_subset hsub,
    List.toFinset_card_of_nodup hnd', List.toFinset_card_of_nodup hnd]
  have hle := Finset.card_le_card hsub'
  rw [List.toFinset_card_of_nodup hnd', List.length_append, List.length_singleton] at hle
  simp only [List.length_append, List.length_singleton]
  omega

/-- A nonnegative residual certifies a new entry and preserves the
subset of edges that the model reports on this call. -/
theorem detect_report_snoc {cfg : Alg2Config} (st : Alg2State cfg)
    {P edge : ℕ} {account residual : ℤ} {reported : List ℕ}
    (hnd : reported.Nodup) (hsub : reported.toFinset ⊆ (algorithm2_detect cfg st).1)
    (he : edge ∈ st.extG.E) (hε : 0 < cfg.ε) (hl : 0 < st.extℓ edge)
    (haccount : (account : ℝ) / (2 : ℝ) ^ P =
      resetReported st.detectAccum reported.toFinset edge)
    (hresidual : residual = account - detectorThreshold P cfg.ε (st.extℓ edge))
    (hready : 0 ≤ residual) :
    (reported ++ [edge]).Nodup ∧
    (reported ++ [edge]).toFinset ⊆ (algorithm2_detect cfg st).1 := by
  obtain ⟨hn, hs, _⟩ := detect_pending_snoc st hnd hsub
    ((detect_residual_pending st he hε hl haccount hresidual).mp hready)
  exact ⟨hn, hs⟩

/-- A ready residual consumes exactly one pending report. -/
theorem detect_report_snoc_pending {cfg : Alg2Config} (st : Alg2State cfg)
    {P edge : ℕ} {account residual : ℤ} {reported : List ℕ}
    (hnd : reported.Nodup) (hsub : reported.toFinset ⊆ (algorithm2_detect cfg st).1)
    (he : edge ∈ st.extG.E) (hε : 0 < cfg.ε) (hl : 0 < st.extℓ edge)
    (haccount : (account : ℝ) / (2 : ℝ)^P =
      resetReported st.detectAccum reported.toFinset edge)
    (hresidual : residual = account - detectorThreshold P cfg.ε (st.extℓ edge))
    (hready : 0 ≤ residual) :
    ((algorithm2_detect cfg st).1 \ (reported ++ [edge]).toFinset).card + 1 =
      ((algorithm2_detect cfg st).1 \ reported.toFinset).card :=
  (detect_pending_snoc st hnd hsub
    ((detect_residual_pending st he hε hl haccount hresidual).mp hready)).2.2

/-- The machine's replacement record represents a zero account for
the reported edge. Its original-direction flow is preserved. -/
theorem detectReset_reported {cfg : Alg2Config} (st : Alg2State cfg)
    {w h P L edge src th heap ret : ℕ} {reported : List ℕ}
    {mem mem' : ℕ → ℕ} (value : PathEdgeValue)
    (hout : (detectResetContract w h value (detectorThreshold P cfg.ε (st.extℓ edge))).post
      [src, th, L, heap] mem ret mem') :
    ∃ v, PathEdgeAt mem' heap h L (some v) ∧ v.originalFlow = value.originalFlow ∧
      v.detector = 0 - detectorThreshold P cfg.ε (st.extℓ edge) ∧
      ((0 : ℤ) : ℝ) / (2 : ℝ) ^ P =
        resetReported st.detectAccum (reported ++ [edge]).toFinset edge := by
  obtain ⟨source, threshold, limbs, dst, hargs, _, hv, _, _⟩ := hout
  simp only [List.cons.injEq, and_true] at hargs
  rcases hargs with ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨_, hv, rfl, (zero_sub _).symm, ?_⟩
  simp [resetReported]

/-- Removing the reported slot from the tree's ready set removes
exactly its external name from the model's pending reports. -/
theorem detect_ready_map_after_report {cfg : Alg2Config} (st : Alg2State cfg)
    {tree : PathTreeState} {reported : Finset ℕ} (slotOf : ℕ → ℕ)
    {edge : ℕ} (hready : pathTreeReady tree (slotOf edge))
    (value : PathEdgeValue) (hneg : value.detector < 0)
    (hinj : Set.InjOn slotOf (st.extG.E : Set ℕ)) (he : edge ∈ st.extG.E)
    (hmap : ∀ e ∈ st.extG.E,
      pathTreeReady tree (slotOf e) ↔ e ∈ (algorithm2_detect cfg st).1 \ reported) :
    let node := slotOf edge
    let read := LinkCut.lctExpose pathPayload (LinkCut.lctExpose pathPayload tree node) node
    ∀ e ∈ st.extG.E, pathTreeReady (pathTreeWrite read node (some value)) (slotOf e) ↔
      e ∈ (algorithm2_detect cfg st).1 \ insert edge reported := by
  dsimp only
  intro e hem
  have hr := pathTreeReady_after_report hready value hneg (slotOf e)
  dsimp only at hr
  rw [hr, hmap e hem]
  simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
  have hne : slotOf e ≠ slotOf edge ↔ e ≠ edge :=
    ⟨fun hn h => hn (congrArg slotOf h), fun hn h => hn (hinj hem he h)⟩
  rw [hne]
  tauto

/-- A forest search finding no nonnegative residual certifies that the
model has no pending reports, provided the represented residuals cover
every live edge. -/
theorem detect_exhausted_of_negative_residuals {cfg : Alg2Config} (st : Alg2State cfg)
    (P : ℕ) (reported : Finset ℕ) (account residual : ℕ → ℤ) (heps : 0 < cfg.ε)
    (hsub : reported ⊆ (algorithm2_detect cfg st).1)
    (hl : ∀ e ∈ st.extG.E, 0 < st.extℓ e)
    (ha : ∀ e ∈ st.extG.E,
      (account e : ℝ) / (2 : ℝ)^P = resetReported st.detectAccum reported e)
    (hr : ∀ e ∈ st.extG.E, residual e = account e - detectorThreshold P cfg.ε (st.extℓ e))
    (hnegative : ∀ e ∈ st.extG.E, residual e < 0) :
    reported = (algorithm2_detect cfg st).1 ∧
      resetReported st.detectAccum reported = (algorithm2_detect cfg st).2.detectAccum := by
  apply detect_exhausted st heps hsub
  intro e he hready
  apply (not_le_of_gt (hnegative e he))
  rw [hr e he, ← detectorThreshold_test P cfg.ε (st.extℓ e) (account e) (hl e he), ha e he]
  exact hready

/-- When the search is exhausted, writing the count produces the
IPM's Detect output and the sequential resets agree with the model. -/
theorem detectFinish_of_exhausted {w : ℕ} (F : MinRatioFormat w) (cfg : Alg2Config)
    {G : MGraph} {m handle heap ret : ℕ} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ}
    {s : (algorithm2_dsWithFailureWith cfg κ).State} {mem mem' : ℕ → ℕ} {reported : List ℕ}
    (hfit : MinRatioStateFits (algorithm2_dsWithFailureWith cfg κ) G F.fmt.limbBits F.limbs F.fmt.precision s)
    (hε : 0 < cfg.ε) (hsub : reported.toFinset ⊆ (algorithm2_detect cfg s).1)
    (hstop : ∀ e ∈ s.extG.E, ¬ cfg.ε ≤ s.extℓ e * resetReported s.detectAccum reported.toFinset e)
    (hout : (detectFinishContract w reported).post [heap, reported.length] mem ret mem') :
    (minRatioMachineContract F (algorithm2_dsWithFailureWith cfg κ) G m κ α rate allocation).post
      2 s [handle, heap] mem (algorithm2_detect cfg s).2 mem' ∧
    resetReported s.detectAccum reported.toFinset = (algorithm2_detect cfg s).2.detectAccum := by
  obtain ⟨heq, hreset⟩ := detect_exhausted s hε hsub hstop
  refine ⟨detectFinish_minRatio_post F cfg hfit ?_ hout, hreset⟩
  intro e
  rw [← List.mem_toFinset, heq]
  exact Finset.mem_filter

end MinCostFlow.MinRatio
