module

public import MinCostFlow.LSF.Program.DecompPhasePre

/-!
# What the decomposition phase keeps

`decompPhase_frame` collects the frames of the eight calls of the decomposition phase
(`DecompPhase.lean`). Below `dBase`, only the two static stretch arrays change. Above the last
scratch array of the stretch pass, nothing changes. The arrays of `decompWTProc` (from `dBase`,
`12 n` words) and the arrays of `rootsStageProc` (from `inR`, `3 n + tM` words) are not written
by the later calls. Below `dBase`, the memory before `rootsStageProc` is the start memory.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-- The frames of the decomposition phase, with the memories after each call. -/
theorem decompPhase_frame {w h C : ℕ} {T₀ : MGraph} {vList : List ℕ} {X : DecompLayout}
    {mem m₁ m₃ m₄ m₅ m₆ m₇ mem₈ : ℕ → ℕ} {v₁ v₄ v₅ v₆ : ℕ}
    (I : DecompPhaseIn w h C T₀ vList X mem)
    (h₁ : (decompWTContract w).post [X.n, X.m0, X.eu, X.ev, X.qOrd, X.auxPar, 0, X.θ, X.dBase] mem
        v₁ m₁)
    (h₃ : (wstrStageContract w h C).post [X.n, X.tM, X.m0, X.k, wstrLB X.n X.D X.Lw, X.Lw, X.Lin,
        X.nOrig, 0, X.logCap, X.lenArr, tOrigIdBase X.tPtr X.vCap X.tM, X.qOrd, X.auxPar,
        X.auxPar + X.n, tPiBase X.tPtr X.vCap X.tM, X.thBase + 7 * X.n, X.eu, X.ev,
        X.auxPar + 3 * X.n, X.auxPar + X.n + X.n, dgEListBase X.gPtr X.vCap X.eCap, X.numS,
        X.denS, X.idPtr] m₁ (wsPt X.idPtr X.n X.tM X.m0 (wstrLB X.n X.D X.Lw) 18) m₃)
    (h₄ : (memCopyContract w).post [X.hiCopy, wsPt X.idPtr X.n X.tM X.m0 (wstrLB X.n X.D X.Lw) 18,
        X.m0] m₃ v₄ m₄)
    (h₅ : (flagMergeContract w).post [X.n, X.cnt, X.m0, X.dBase + 11 * X.n, X.repPtr, X.vIdx,
        X.hiCopy, X.eu, X.ev, X.inR] m₄ v₅ m₅)
    (h₆ : (rootsStageContract w).post [X.n, X.tM, 0, X.qOrd, X.auxPar, X.auxPar + X.n,
        tPiBase X.tPtr X.vCap X.tM, X.thDst, X.thBase + 7 * X.n, X.D, X.inR, X.inR + X.n,
        X.inR + X.n + X.n, X.inR + X.n + X.n + X.tM] m₅ v₆ m₆)
    (h₇ : wstrCopyEdgesPost X.numSt X.numS (dgEListBase X.gPtr X.vCap X.eCap) X.m0 X.Lw
      (X.eCap * X.Lw) m₆ m₇)
    (h₈ : wstrCopyEdgesPost X.denSt X.denS (dgEListBase X.gPtr X.vCap X.eCap) X.m0 X.Lw
      (X.eCap * X.Lw) m₇ mem₈) :
    (∀ a < X.dBase, (a < X.numSt ∨ X.denSt + X.eCap * X.Lw ≤ a) → mem₈ a = mem a) ∧
    (∀ a, wsPt X.idPtr X.n X.tM X.m0 (wstrLB X.n X.D X.Lw) 18 + X.m0 ≤ a → mem₈ a = mem a) ∧
    (∀ a, X.dBase ≤ a → a < X.dBase + 12 * X.n → mem₈ a = m₁ a) ∧
    (∀ a, X.inR ≤ a → a < X.inR + 3 * X.n + X.tM → mem₈ a = m₆ a) ∧
    (∀ a < X.dBase, m₅ a = mem a) ∧
    (∀ a, X.dBase ≤ a → a < X.dBase + 12 * X.n → m₅ a = m₁ a) := by
  have L13 := I.L13; have L14 := I.L14; have L15 := I.L15; have L16 := I.L16
  have L17 := I.L17; have L18 := I.L18
  have hid : X.idPtr ≤ wsPt X.idPtr X.n X.tM X.m0 (wstrLB X.n X.D X.Lw) 18 :=
    wsPt_mono X.idPtr X.n X.tM X.m0 _ (Nat.zero_le 18)
  have hdS : X.denS = X.numS + X.eCap * X.Lw := rfl
  obtain ⟨_, _, _, _, _, _, _, _, _, heq₁, -, hfr₁, -⟩ := h₁
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₁
  obtain ⟨-, hW⟩ := h₃
  rw [wstrStageArgs_eq] at hW
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, heqW, -, hWP⟩ := hW
  simp only [List.cons.injEq, and_true] at heqW
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩ := heqW
  obtain ⟨_, -, -, -, -, -, -, hfrW, hfrH, -⟩ := hWP
  have hm₃ : ∀ a < X.numS, m₃ a = m₁ a := fun a ha =>
    hfrW a (by omega) fun t _ => ⟨Or.inl (by omega), Or.inl (by omega)⟩
  obtain ⟨_, _, _, heq₄, -, -, hfr₄⟩ := h₄
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl⟩ := heq₄
  obtain ⟨_, _, _, _, _, _, _, _, _, _, heq₅, -, hfr₅, -⟩ := h₅
  simp only [List.cons.injEq, and_true] at heq₅
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₅
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, heq₆, -, hfr₆, -⟩ := h₆
  simp only [List.cons.injEq, and_true] at heq₆
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₆
  obtain ⟨-, hfr₇⟩ := h₇
  obtain ⟨-, hfr₈⟩ := h₈
  -- the last two copies write only the static stretch arrays
  have h86 : ∀ a, (a < X.numSt ∨ X.denSt + X.eCap * X.Lw ≤ a) → mem₈ a = m₆ a := fun a ha => by
    rw [hfr₈ a (by omega), hfr₇ a (by omega)]
  -- below the copied flags the memory before the roots pass is the memory after the stretch pass
  have h53 : ∀ a < X.hiCopy, m₅ a = m₃ a := fun a ha => by
    rw [hfr₅ a (Or.inl (by omega)), hfr₄ a (Or.inl ha)]
  refine ⟨fun a ha1 ha2 => ?_, fun a ha => ?_, fun a ha1 ha2 => ?_, fun a ha1 ha2 => ?_,
    fun a ha => ?_, fun a ha1 ha2 => ?_⟩
  · rw [h86 a ha2, hfr₆ a (Or.inl (by omega)) (Or.inl (by omega)), h53 a (by omega),
      hm₃ a (by omega), hfr₁ a (Or.inl ha1)]
  · rw [h86 a (Or.inr (by omega)), hfr₆ a (Or.inr (by omega)) (Or.inr (by omega)),
      hfr₅ a (Or.inr (by omega)), hfr₄ a (Or.inr (by omega)), hfrH a ha,
      hfr₁ a (Or.inr (by omega))]
  · rw [h86 a (Or.inr (by omega)), hfr₆ a (Or.inl (by omega)) (Or.inl (by omega)),
      h53 a (by omega), hm₃ a (by omega)]
  · rw [h86 a (Or.inr (by omega))]
  · rw [h53 a (by omega), hm₃ a (by omega), hfr₁ a (Or.inl ha)]
  · rw [h53 a (by omega), hm₃ a (by omega)]

end

end MinCostFlow.LSF.Program
