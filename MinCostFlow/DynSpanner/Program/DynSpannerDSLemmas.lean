module

public import MinCostFlow.DynSpanner.Program.DynSpannerDSDefs

/-!
# The data structure of Theorem 8.2: lemmas about the representation

This file proves the facts about `dynSpannerRep` that do not run a program.

* `dynSpannerStateAt_of_agree_foot` and `dynSpannerRep_local`: the state block and the
  representation depend only on the words of the footprint `metaFoot`.
* `theorem82Clauses_of`: the clauses of Theorem 8.2 hold for every history that the data
  structure can reach, by `theorem_8_2`.
* `DSHist.genBound_append`: how the bound on the generation word grows with a batch.
* `snapInv_of_history`: the invariant `SnapInv` that the batch loop asks for, by `runInv_all`.
* `dsUpdateAmortCost_le`: the amortized cost of an update in the form of Theorem 8.2.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

public section

/-- The state block depends only on the words of its footprint `metaFoot b x`. -/
theorem dynSpannerStateAt_of_agree_foot {L vCap eCap b : ℕ} {mem mem' : ℕ → ℕ}
    {x : DynSpannerMeta L} {st : DynSpannerState L}
    (hState : DynSpannerStateAt L vCap eCap b mem x st)
    (hag : ∀ a, metaFoot b x a → mem' a = mem a) :
    DynSpannerStateAt L vCap eCap b mem' x st := by
  have hxv : x.vCap = vCap := hState.1
  have hxe : x.eCap = eCap := hState.2.1
  have hfix : ∀ a, b ≤ a → a < b + dsFixedSize L vCap eCap → mem' a = mem a := fun a h1 h2 =>
    hag a (Or.inl ⟨h1, by rw [hxv, hxe]; exact h2⟩)
  have hgen := (stepZero_fixed_lt b L vCap eCap).1 dsGenOff (by decide)
  have hgen_eq : mem' (b + dsGenOff) = mem (b + dsGenOff) := hfix _ hgen.1 hgen.2
  obtain ⟨hgo, -, hG_e, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hek, hks_top⟩ :=
    collectD_lt_eStamp_bounds b L vCap eCap
  have hb_est : b ≤ dsEStampBase b L vCap eCap :=
    le_trans (Nat.le_add_right _ _)
      (le_of_lt (lt_of_lt_of_le hgo (le_trans (Nat.le_add_right _ _) hG_e)))
  refine dynSpannerStateAt_of_collectD_foot hState (le_of_eq hgen_eq.symm) (fun e he => ?_)
    (fun a _ _ hdom => ?_)
  · have hlt : dsEStampBase b L vCap eCap + e < b + dsFixedSize L vCap eCap := by
      rw [← hek] at hks_top; omega
    rw [hfix _ (le_trans hb_est (Nat.le_add_right _ _)) hlt, hgen_eq]
    exact (hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 e he).1
  · rcases hdom with ⟨h1, h2⟩ | hh
    · exact hfix a h1 h2
    · exact hag a (Or.inr hh)

/-- The representation of the data structure is local: it depends only on the words of the
footprint. -/
theorem dynSpannerRep_local (P : DSParams) : (dynSpannerRep P).Local := by
  intro b s x mem mem' hag
  refine ⟨fun h => ?_, rfl⟩
  obtain ⟨hx, ⟨hL, hV, hm, hE, hB, hds, hsp, hState, hRev, hgen⟩, hp⟩ := h
  have hgen' := (stepZero_fixed_lt b P.L P.vCap P.eCap).1 dsGenOff (by decide)
  have hgen_eq : mem (b + dsGenOff) = mem' (b + dsGenOff) :=
    hag _ (Or.inl ⟨hgen'.1, by rw [hState.1, hState.2.1]; exact hgen'.2⟩)
  exact ⟨hx, ⟨hL, hV, hm, hE, hB, hds, hsp,
    dynSpannerStateAt_of_agree_foot hState (fun a ha => (hag a ha).symm), hRev,
    hgen_eq ▸ hgen⟩, hp⟩

/-- The clauses of Theorem 8.2 for a history of valid batches, by `theorem_8_2` applied to the
sparsifier of the data structure (`canonicalSparsify_spec_absorb`). -/
theorem theorem82Clauses_of (P : DSParams) {G₀ : MGraph} {Us : List (List Update)}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ P.L) (hGm₀ : G₀.m ≤ P.mMax)
    (hBV : G₀.BatchIsValid Us.flatten) (hds : ∀ u ∈ Us.flatten, isDelOrSplit u)
    (hSplits : batchSplitCount Us.flatten ≤ P.splitBound) :
    Theorem82Clauses G₀ P.L P.splitBound (dsSparsifyParams P) (canonicalSparsify P.impl) Us :=
  theorem_8_2 hVG₀ hL hGm₀ (canonicalSparsify_spec_absorb P.impl P.mMax) hBV hds hSplits

/-- `SnapInv` at every time up to the end of a valid list of updates, by `runInv_all`. -/
theorem snapInv_of_history (P : DSParams) {G₀ : MGraph} {q : ℕ} {us : List Update}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ P.L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ P.mMax)
    (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u) :
    ∀ s ≤ us.length, SnapInv G₀ P.L q P.mMax (canonicalSparsifyParams P.impl P.mMax).absorbTime
      (canonicalSparsify P.impl) us s := fun s hs =>
  (runInv_all hVG₀ hL hq hGm₀ (canonicalSparsify_spec_absorb P.impl P.mMax) hBV hds s hs).1

/-- The batch read by `decodeBatchBody mem n` has `n` updates. -/
theorem decodeBatchBody_length (mem : ℕ → ℕ) :
    ∀ (n a : ℕ) (G : MGraph), (decodeBatchBody mem n a G).1.length = n
  | 0, _, _ => rfl
  | n + 1, a, G => by
    simp only [decodeBatchBody, List.length_cons, decodeBatchBody_length mem n]

/-- The model state of `⟨G₀, Us ++ [U]⟩` is the model state of the loop over `U`. -/
theorem DSHist.state_append (P : DSParams) (s : DSHist) (U : List Update) :
    (DSHist.state P ⟨s.G₀, s.Us ++ [U]⟩) =
      runState (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U)
        (s.flat.length + U.length) := by
  simp only [DSHist.state, DSHist.flat, DSHist.q, List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.length_append]

/-- The bound on the generation word after a batch `U`: the bound before it plus the bound
`dsUpdateLoopGen` of the batch loop. -/
theorem DSHist.genBound_append (P : DSParams) (s : DSHist) (U : List Update) :
    DSHist.genBound P ⟨s.G₀, s.Us ++ [U]⟩ =
      s.genBound P + dsUpdateLoopGen s.G₀ P.impl P.L (s.q P) (s.flat ++ U) U.length
        s.flat.length := by
  have hflat : (⟨s.G₀, s.Us ++ [U]⟩ : DSHist).flat = s.flat ++ U := by
    simp [DSHist.flat]
  have hq : (⟨s.G₀, s.Us ++ [U]⟩ : DSHist).q P = s.q P := rfl
  simp only [DSHist.genBound, hflat, hq, List.length_append, Finset.sum_range_add,
    dsUpdateLoopGen, List.length_singleton]
  have hpre : ∑ r ∈ Finset.range s.flat.length,
      dsStepGenAt s.G₀ P.impl P.L (s.q P) (s.flat ++ U) r =
      ∑ r ∈ Finset.range s.flat.length, dsStepGenAt s.G₀ P.impl P.L (s.q P) s.flat r :=
    Finset.sum_congr rfl fun r hr =>
      dsStepGenAt_append s.G₀ P.impl P.L (s.q P) s.flat U (Finset.mem_range.mp hr)
  rw [hpre]
  omega

/-- **The amortized cost of an update in the form of Theorem 8.2.** A batch `U` of `W` words on
the history `s` costs at most `C · 90 L n^{1/L} K₁ E_L Δ₁ Λ · Enc(U) + 1440 W + 506`, with
`C = dsAmortConst impl` and `n = n₀ + splitBound`. -/
theorem dsUpdateAmortCost_le (P : DSParams) (s : DSHist) (args : List ℕ) (mem : ℕ → ℕ) :
    (dsUpdateAmortCost P s args mem : ℝ) ≤
      (dsAmortConst P.impl : ℝ) * dsBatchRate P.impl P.mMax P.L (s.G₀.n + P.splitBound) s.G₀ *
          ((s.G₀.applyBatch s.flat).batchEnc (opBatch P s args mem).1 : ℝ) +
        1440 * (opWords args : ℝ) + 506 := by
  have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (dsAmortConst P.impl : ℝ) *
      dsBatchRate P.impl P.mMax P.L (s.G₀.n + P.splitBound) s.G₀ *
        ((s.G₀.applyBatch s.flat).batchEnc (opBatch P s args mem).1 : ℝ) by
    obtain ⟨hEL1, -⟩ := expFactor_bounds (canonicalSparsifyParams P.impl P.mMax).absorbTime.hγ_c
      (canonicalSparsifyParams P.impl P.mMax).absorbTime.hγ_ℓ P.L s.G₀.maxDeg
    have h1 := (canonicalSparsifyParams P.impl P.mMax).absorbTime.hK_t
    have h2 := (canonicalSparsifyParams P.impl P.mMax).absorbTime.hK_s
    have h3 : (1 : ℝ) ≤ ((s.G₀.n + P.splitBound : ℕ) : ℝ) + (s.G₀.m : ℝ) + 2 := by
      linarith [Nat.cast_nonneg (α := ℝ) (s.G₀.n + P.splitBound), Nat.cast_nonneg (α := ℝ) s.G₀.m]
    have h4 := Real.log_nonneg h3
    simp only [dsBatchRate]
    have h5 : (0 : ℝ) ≤ 3 ^ ((P.L + 1) * (P.L + 2) / 2 + P.L + 2) *
        (canonicalSparsifyParams P.impl P.mMax).absorbTime.γ_c ^ (P.L + 1) *
        (canonicalSparsifyParams P.impl P.mMax).absorbTime.γ_ℓ ^
          ((P.L + 1) * (P.L + 2) / 2 + 2) := by linarith
    have h6 : (0 : ℝ) ≤ (canonicalSparsifyParams P.impl P.mMax).absorbTime.K_t +
        (canonicalSparsifyParams P.impl P.mMax).absorbTime.K_s + 1 := by linarith
    have h7 : (0 : ℝ) ≤ 1 + Real.log (((s.G₀.n + P.splitBound : ℕ) : ℝ) + (s.G₀.m : ℝ) + 2) := by
      linarith
    positivity)
  have hdef : dsUpdateAmortCost P s args mem =
      dsBatchCharge P.impl P.mMax P.L (s.G₀.n + P.splitBound) s.G₀ (s.G₀.applyBatch s.flat)
        (opBatch P s args mem).1 + 1440 * opWords args + 485 + dsUpdateOpOverhead := rfl
  rw [hdef]
  simp only [dsBatchCharge, dsUpdateOpOverhead] at h ⊢
  push_cast
  linarith

end

end MinCostFlow.DynSpanner.Program
