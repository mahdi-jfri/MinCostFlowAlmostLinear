module

public import MinCostFlow.MinRatio.DetectForestAccounts
public import MinCostFlow.MinRatio.DetectSlotStep

/-!
# Detect lookup tables

The reporting loop in Theorem 5.1 (pages 29–30) identifies a ready
edge and resets its account. The slot names, inverse names, and
threshold pointers give these arguments without scanning the graph.
-/

public section
namespace MinCostFlow.MinRatio

open Chain WordRAM

/-- For every live edge, the ready-slot lookup yields its external name
and a pointer to the stored threshold numerator. -/
@[expose] def DetectTablesAt {cfg : Alg2Config} (model : Alg2State cfg)
    (mem : ℕ → ℕ) (names inverse thresholds h L P : ℕ)
    (slotOf internalOf thresholdOf : ℕ → ℕ) : Prop :=
  ∀ e ∈ model.extG.E,
    mem (names + slotOf e) = internalOf e ∧
    mem (inverse + internalOf e) = e ∧
    mem (thresholds + slotOf e) = thresholdOf e ∧
    PathIntAt mem (thresholdOf e) h L (detectorThreshold P cfg.ε (model.extℓ e))

/-- Search and point writes preserve the lookup tables when their
cells are outside the tree footprint and the current report cell. -/
theorem DetectTablesAt.congr {cfg : Alg2Config} {model : Alg2State cfg}
    {mem mem' : ℕ → ℕ} {names inverse thresholds h L P : ℕ}
    {slotOf internalOf thresholdOf : ℕ → ℕ}
    (ht : DetectTablesAt model mem names inverse thresholds h L P slotOf internalOf thresholdOf)
    (hframe : ∀ e ∈ model.extG.E, ∀ a,
      (a = names + slotOf e ∨ a = inverse + internalOf e ∨ a = thresholds + slotOf e ∨
        (thresholdOf e ≤ a ∧ a < thresholdOf e + L)) → mem' a = mem a) :
    DetectTablesAt model mem' names inverse thresholds h L P slotOf internalOf thresholdOf := by
  intro e he
  obtain ⟨hn, hi, hp, ht⟩ := ht e he
  refine ⟨(hframe e he _ (Or.inl rfl)).trans hn,
    (hframe e he _ (Or.inr (Or.inl rfl))).trans hi,
    (hframe e he _ (Or.inr (Or.inr (Or.inl rfl)))).trans hp, ?_⟩
  exact ht.congr (fun j hj => hframe e he _ (Or.inr (Or.inr (Or.inr (by omega)))))

/-- The two loads used by the ready branch yield the external name. -/
theorem DetectTablesAt.externalName {cfg : Alg2Config} {model : Alg2State cfg}
    {mem : ℕ → ℕ} {names inverse thresholds h L P e slot : ℕ}
    {slotOf internalOf thresholdOf : ℕ → ℕ}
    (ht : DetectTablesAt model mem names inverse thresholds h L P slotOf internalOf thresholdOf)
    (he : e ∈ model.extG.E) (hs : slotOf e = slot) :
    mem (inverse + mem (names + slot)) = e := by
  obtain ⟨hn, hi, _, _⟩ := ht e he
  rw [← hs, hn, hi]

/-- The table and read-workspace representations supply the reset
and append preconditions for the selected live edge. -/
theorem DetectTablesAt.slotStep_pre {cfg : Alg2Config} {model : Alg2State cfg}
    {mem : ℕ → ℕ} {w names inverse thresholds h L P e slot report cursor src heap : ℕ}
    {slotOf internalOf thresholdOf : ℕ → ℕ} {written : List ℕ} {value : PathEdgeValue}
    (ht : DetectTablesAt model mem names inverse thresholds h L P slotOf internalOf thresholdOf)
    (he : e ∈ model.extG.E) (hs : slotOf e = slot)
    (hcursor : cursor = report + written.length)
    (hnames : names + slot < cursor) (hinverse : inverse + internalOf e < cursor)
    (heword : e < 2 ^ w) (hcurheap : cursor < heap)
    (hthree : 3 < 2 ^ w)
    (hreadEnd : src + (2 + 4 * L) ≤ heap) (hthEnd : thresholdOf e + L ≤ heap)
    (hresetEnd : heap + (2 + 4 * L) < 2 ^ w)
    (hread : PathEdgeAt mem src h L (some value))
    (heps : 0 < cfg.ε) (hlen : 0 < model.extℓ e)
    (hlist : ListAt mem report written) (hzero : ZeroFrom mem heap) :
    mem (thresholds + slot) = thresholdOf e ∧
      (detectSlotStepContract w h report written value
        (detectorThreshold P cfg.ε (model.extℓ e))).pre
        [names, inverse, slot, cursor, src, thresholdOf e, L, heap] mem := by
  obtain ⟨hn, hinv, hp, hth⟩ := ht e he
  rw [hs] at hn hp
  have hheap : heap < 2 ^ w := Nat.lt_of_le_of_lt (Nat.le_add_right ..) hresetEnd
  have hfit := Num.intVal_fits hth.1
  rw [hth.2] at hfit
  have hpos := detectorThreshold_pos P cfg.ε (model.extℓ e) heps hlen
  have hfits : Num.Fits h L (-detectorThreshold P cfg.ε (model.extℓ e)) := by
    unfold Num.Fits at hfit ⊢
    obtain ⟨_, hupper⟩ := hfit
    omega
  exact ⟨hp, names, inverse, slot, cursor, src, thresholdOf e, L, heap, rfl,
    ⟨src, thresholdOf e, L, heap, rfl, hthree, hreadEnd, hthEnd, hresetEnd, hread, hth, hfits, hzero⟩,
    ⟨names, inverse, slot, cursor, rfl, hcursor, hnames, by rwa [hn], hcurheap,
      hheap, by rwa [hn, hinv], hlist, hzero⟩⟩

end MinCostFlow.MinRatio
