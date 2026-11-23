module

public import MinCostFlow.LSF.Program.OrderPhasePre

/-!
# What the order phase keeps

`orderPhase_frame` collects the frames of the five calls of the order phase: outside the aux
arrays, the `T` block, the scratch areas of the rooting and of the order, and the two outputs of
the `T_H` stage, the memory after the phase is the memory before it. `orderPhase_aux` says that
the arrays of the rooting call (parents, depths, the ancestor table, the order `Q`) survive the
later calls; only the parent edge of the root changes, to `0`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-- The frames of the order phase, with the memories after each call. -/
theorem orderPhase_frame {w h : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ} {X : OrderLayout}
    {mem mem₁ mem₃ mem₄ mem₅ : ℕ → ℕ} {v₁ v₃ v₄ v₅ : ℕ}
    (I : OrderPhaseIn w h G₀ T₀ vList eList X mem)
    (h₁ : (rootStageContract w).post
        [X.n, X.tM, X.tTail, X.tHead, 0, X.rtOut, X.sPtr, X.auxPar, X.logCap] mem v₁ mem₁)
    (h₃ : (orderStageContract w h G₀ vList eList).post
        [X.n, 0, X.m0, dgEListBase X.gPtr X.vCap X.eCap, dgETailSlotBase X.gPtr X.vCap X.eCap,
          dgEHeadSlotBase X.gPtr X.vCap X.eCap, dgIntToExtBase X.gPtr X.vCap, X.vIdx, X.eu, X.ev,
          X.qPtr, X.Kq, X.dPtr, X.K, X.tmpPtr, X.logCap, X.auxPar + 3 * X.n,
          X.auxPar + X.n + X.n, X.auxPar, X.qOrd, X.auxPar + X.n, X.arrPtr, X.scratchPtr,
          tPiBase X.tPtr X.vCap X.tM, X.minPtr]
        (Function.update mem₁ (X.auxPar + X.n) 0) v₃ mem₃)
    (h₄ : (tStageContract w G₀ T₀ vList).post [X.tPtr, X.vCap, X.eCap, X.tM, X.vListPtr,
        X.tOrigSrc, X.tTail, X.tHead, X.n, X.nOrig, tOrigIdBase X.tPtr X.vCap X.tM,
        tDgTPtr X.tPtr] mem₃ v₄ mem₄)
    (h₅ : (thStageContract w T₀ vList).post
        [X.n, X.qOrd, X.auxPar, X.auxPar + X.n + X.n, X.thBase, 0, X.thDst] mem₄ v₅ mem₅) :
    (∀ a, (a < X.tPtr ∨ (X.tPtr + tBlockSize X.vCap X.eCap X.tM ≤ a ∧ a < X.auxPar) ∨
        (X.minPtr + X.n * X.logCap ≤ a ∧ a < X.thDst) ∨ (X.thDst + X.n ≤ a ∧ a < X.rtOut) ∨
        (X.sPtr + 4 * X.n + 2 * X.tM ≤ a ∧ a < X.eu) ∨ (X.ev + X.m0 ≤ a ∧ a < X.dPtr) ∨
        (X.scratchPtr + X.n ≤ a ∧ a < X.thBase) ∨ X.thBase + 8 * X.n ≤ a) → mem₅ a = mem a) ∧
    (∀ a, X.auxPar ≤ a → a < X.minPtr → a ≠ X.auxPar + X.n → mem₅ a = mem₁ a) ∧
    (∀ a, X.sPtr ≤ a → a < X.sPtr + 4 * X.n + 2 * X.tM → mem₅ a = mem₁ a) ∧
    (∀ a, X.tPtr + tBlockSize X.vCap X.eCap X.tM ≤ a → (a < X.thDst ∨ X.thDst + X.n ≤ a) →
      (a < X.thBase ∨ X.thBase + 8 * X.n ≤ a) → mem₅ a = mem₃ a) ∧
    (∀ a, X.tPtr ≤ a → a < X.tPtr + tBlockSize X.vCap X.eCap X.tM → mem₅ a = mem₄ a) ∧
    mem₅ (X.auxPar + X.n) = 0 := by
  have hn := I.hn2; have hmin := I.hmin
  have l1 := I.l1; have l2 := I.l2; have l3 := I.l3; have l4 := I.l4; have l5 := I.l5
  have l6 := I.l6; have l7 := I.l7; have l8 := I.l8; have l9 := I.l9; have l10 := I.l10
  have l11 := I.l11; have l12 := I.l12; have l13 := I.l13; have l14 := I.l14; have l15 := I.l15
  have l16 := I.l16; have l17 := I.l17; have l18 := I.l18; have l19 := I.l19
  obtain ⟨ht1, ht2⟩ := I.tPi_le
  have ht0 : X.tPtr ≤ tPiBase X.tPtr X.vCap X.tM := by
    simp only [tPiBase, tOrigIdBase, tDgTPtr]; omega
  have ht3 : tPiBase X.tPtr X.vCap X.tM + X.tM ≤ X.tPtr + tBlockSize X.vCap X.eCap X.tM := by
    simp only [tPiBase, tOrigIdBase, tDgTPtr, tBlockSize]; omega
  have hl := (show 1 ≤ X.logCap by rw [I.hlog]; unfold auxLogCap; omega)
  have hnL : X.n ≤ X.n * X.logCap := Nat.le_mul_of_pos_right _ hl
  obtain ⟨_, _, _, _, _, _, _, _, _, tl, hd, heq, -, -, hR, -, -, hfr⟩ := h₁
  simp only [List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq
  have hF2 := orderPhase_frame₂ I hfr
  have hpe : ∀ y < X.n, y ≠ 0 →
      Function.update mem₁ (X.auxPar + X.n) 0 (X.auxPar + X.n + y) < X.tM := by
    intro y hy hy0
    rw [Function.update_of_ne (by omega)]
    exact (hR.step y hy hy0).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, heq₃, -, -, -,
    -, -, hfr₃⟩ := h₃
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl, rfl, -, -, -, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₃
  have hF3 : ∀ a, (a < tPiBase X.tPtr X.vCap X.tM ∨ tPiBase X.tPtr X.vCap X.tM + X.tM ≤ a) →
      (a < X.eu ∨ X.ev + X.m0 ≤ a) → (a < X.dPtr ∨ X.scratchPtr + X.n ≤ a) →
      (a < X.minPtr ∨ X.minPtr + X.n * X.logCap ≤ a) →
      mem₃ a = Function.update mem₁ (X.auxPar + X.n) 0 a :=
    fun a h1 h2 h3 h4 => hfr₃ a h2 h3 h4 fun y hy hy0 => by have := hpe y hy hy0; omega
  obtain ⟨_, _, _, _, _, _, _, _, _, _, heq₄, -, -, -, hfr₄⟩ := h₄
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, -, -⟩ := heq₄
  obtain ⟨_, _, _, _, _, _, _, heq₅, -, -, -, -, hfr₅⟩ := h₅
  simp only [List.cons.injEq, and_true] at heq₅
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₅
  have hqo : X.qOrd = X.sPtr + X.n + 2 * X.tM + X.n := rfl
  -- above the `T` block and outside the outputs of the `T_H` stage
  have h54 : ∀ a, X.tPtr + tBlockSize X.vCap X.eCap X.tM ≤ a → (a < X.thDst ∨ X.thDst + X.n ≤ a) →
      (a < X.thBase ∨ X.thBase + 8 * X.n ≤ a) → mem₅ a = mem₃ a := fun a h0 h1 h2 => by
    rw [hfr₅ a h1 h2, hfr₄ a (Or.inr h0)]
  refine ⟨fun a ha => ?_, fun a h1 h2 h3 => ?_, fun a h1 h2 => ?_, h54,
    fun a h1 h2 => ?_, ?_⟩
  · rcases ha with ha | ha | ha | ha | ha | ha | ha | ha
    · rw [hfr₅ a (Or.inl (by omega)) (Or.inl (by omega)), hfr₄ a (Or.inl ha),
        hF3 a (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]
      exact hF2 a (Or.inl (by omega))
    all_goals
      rw [h54 a (by omega) (by omega) (by omega),
        hF3 a (Or.inr (by omega)) (by omega) (by omega) (by omega)]
      exact hF2 a (by omega)
  · rw [h54 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
      hF3 a (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)),
      Function.update_of_ne h3]
  · rw [h54 a (by omega) (Or.inr (by omega)) (Or.inl (by omega)),
      hF3 a (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega)),
      Function.update_of_ne (by omega)]
  · rw [hfr₅ a (Or.inl (by omega)) (Or.inl (by omega))]
  · rw [h54 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
      hF3 _ (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)),
      Function.update_self]

end

end MinCostFlow.LSF.Program
