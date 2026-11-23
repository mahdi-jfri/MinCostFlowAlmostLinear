module

public import MinCostFlow.LinkCut.Path.Layout
public import MinCostFlow.LinkCut.Path.Narrow
public import MinCostFlow.MinRatio.PathPayloadFits
public import WordRAM.CopyWords
public import WordRAM.Tactic

/-!
# Copying an edge value out in fewer limbs

A point read returns a node's value in the interface width `L`, while the node record keeps it
in `K ≥ L` limbs. `readValBody` copies the header and direction words and the low `L` limbs of
each of the four numbers. When the numbers fit in `L` limbs this is exact (`intVal_low_of_fits`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Path

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio

/-- The address `base + c + d X`, with the base in register `rb` and `X` in register `r`. -/
abbrev atR (rb r c d : ℕ) : Expr :=
  .bin .add (.reg rb) (.bin .add (.const c) (.bin .mul (.const d) (.reg r)))

/-- `readVal [src, dst, K, L]`: copy the `K`-limb edge value at `src` to an `L`-limb one at
`dst`. -/
def readValBody (copyProc : ℕ) : Stmt :=
  .call 4 copyProc [.reg 0, .reg 1, .const 2] ;;
  .call 4 copyProc [.bin .add (.reg 0) (.const 2), .bin .add (.reg 1) (.const 2), .reg 3] ;;
  .call 4 copyProc [.bin .add (.reg 0) (.bin .add (.const 2) (.reg 2)),
    .bin .add (.reg 1) (.bin .add (.const 2) (.reg 3)), .reg 3] ;;
  .call 4 copyProc [atR 0 2 2 2, atR 1 3 2 2, .reg 3] ;;
  .call 4 copyProc [atR 0 2 2 3, atR 1 3 2 3, .reg 3] ;;
  .ret (.const 0)

theorem readValBody_noRand (b : ℕ) : (readValBody b).NoRand := by
  simp [readValBody, Stmt.NoRand]

/-- The contract of `readValBody`. The two blocks do not overlap. -/
def readValContract (w h K L : ℕ) : Contract where
  pre args mem := ∃ src dst, args = [src, dst, K, L] ∧ 1 < 2 ^ w ∧ L ≤ K ∧
    src + (2 + 4 * K) < 2 ^ w ∧ dst + (2 + 4 * L) < 2 ^ w ∧
    (src + (2 + 4 * K) ≤ dst ∨ dst + (2 + 4 * L) ≤ src) ∧
    ∃ v, PathEdgeAt mem src h K v ∧ PathEdgeFits h L v
  post args mem _ mem' :=
    (∀ y, ¬ (args.getD 1 0 ≤ y ∧ y < args.getD 1 0 + (2 + 4 * L)) → mem' y = mem y) ∧
    ∀ v, PathEdgeAt mem (args.getD 0 0) h K v → PathEdgeFits h L v →
      PathEdgeAt mem' (args.getD 1 0) h L v
  cost _ _ := 68 * L + 260

/-- One narrowed number. -/
theorem pathIntAt_low {m m' : ℕ → ℕ} {src dst h K L : ℕ} {z : ℤ} (hLK : L ≤ K)
    (hz : PathIntAt m src h K z) (hf : Fits h L z)
    (hc : ∀ i < L, m' (dst + i) = m (src + i)) : PathIntAt m' dst h L z := by
  refine ⟨fun i hi => by rw [hc i hi]; exact hz.1 i (by omega), ?_⟩
  rw [intVal_congr hc, intVal_low_of_fits hLK hz.1 (by rw [hz.2]; exact hf), hz.2]

theorem readVal_meetsContract {w h K L f copyProc : ℕ} {p : Program}
    (hb : p.procs[f]? = some (readValBody copyProc))
    (hcopy : MeetsContract w p copyProc (copyWordsContract w)) :
    MeetsContract w p f (readValContract w h K L) := by
  apply meetsContract_of_runs hb
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨src, dst, rfl, hw, hLK, hsw, hdw, hdis, v, hv, hfv⟩
  apply runs_start_le
  unfold readValBody
  refine runs_seq_call_le hcopy (vs := [src, dst, 2]) (by eval_expr) (by
      intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨_, _, _, rfl, hw, by omega, by omega, by omega⟩ ?_
  rintro v₁ m₁ pos₁ ⟨s₁, d₁, l₁, heq₁, -, hc₁, ho₁⟩
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl⟩ := heq₁
  change ∀ i < 2, m₁ (dst + i) = mem (src + i) at hc₁
  change ∀ y, y < dst ∨ dst + 2 ≤ y → m₁ y = mem y at ho₁
  refine runs_seq_call_le hcopy (vs := [src + 2, dst + 2, L]) (by eval_expr) (by
      intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨_, _, _, rfl, hw, by omega, by omega, by omega⟩ ?_
  rintro v₂ m₂ pos₂ ⟨s₂, d₂, l₂, heq₂, -, hc₂, ho₂⟩
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl⟩ := heq₂
  change ∀ i < L, m₂ (dst + 2 + i) = m₁ (src + 2 + i) at hc₂
  change ∀ y, y < dst + 2 ∨ dst + 2 + L ≤ y → m₂ y = m₁ y at ho₂
  refine runs_seq_call_le hcopy (vs := [src + (2 + K), dst + (2 + L), L]) (by eval_expr) (by
      intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨_, _, _, rfl, hw, by omega, by omega, by omega⟩ ?_
  rintro v₃ m₃ pos₃ ⟨s₃, d₃, l₃, heq₃, -, hc₃, ho₃⟩
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl⟩ := heq₃
  change ∀ i < L, m₃ (dst + (2 + L) + i) = m₂ (src + (2 + K) + i) at hc₃
  change ∀ y, y < dst + (2 + L) ∨ dst + (2 + L) + L ≤ y → m₃ y = m₂ y at ho₃
  refine runs_seq_call_le hcopy (vs := [src + (2 + 2 * K), dst + (2 + 2 * L), L])
    (by eval_expr) (by
      intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨_, _, _, rfl, hw, by omega, by omega, by omega⟩ ?_
  rintro v₄ m₄ pos₄ ⟨s₄, d₄, l₄, heq₄, -, hc₄, ho₄⟩
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl⟩ := heq₄
  change ∀ i < L, m₄ (dst + (2 + 2 * L) + i) = m₃ (src + (2 + 2 * K) + i) at hc₄
  change ∀ y, y < dst + (2 + 2 * L) ∨ dst + (2 + 2 * L) + L ≤ y → m₄ y = m₃ y at ho₄
  refine runs_seq_call_le hcopy (vs := [src + (2 + 3 * K), dst + (2 + 3 * L), L])
    (by eval_expr) (by
      intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨_, _, _, rfl, hw, by omega, by omega, by omega⟩ ?_
  rintro v₅ m₅ pos₅ ⟨s₅, d₅, l₅, heq₅, -, hc₅, ho₅⟩
  simp only [List.cons.injEq, and_true] at heq₅
  obtain ⟨rfl, rfl, rfl⟩ := heq₅
  change ∀ i < L, m₅ (dst + (2 + 3 * L) + i) = m₄ (src + (2 + 3 * K) + i) at hc₅
  change ∀ y, y < dst + (2 + 3 * L) ∨ dst + (2 + 3 * L) + L ≤ y → m₅ y = m₄ y at ho₅
  -- Cells outside the destination keep their value; source cells in particular.
  have hout : ∀ y, ¬ (dst ≤ y ∧ y < dst + (2 + 4 * L)) → m₅ y = mem y := fun y hy => by
    rw [ho₅ y (by omega), ho₄ y (by omega), ho₃ y (by omega), ho₂ y (by omega),
      ho₁ y (by omega)]
  have hsrc : ∀ i < 2 + 4 * K, m₄ (src + i) = mem (src + i) ∧ m₃ (src + i) = mem (src + i) ∧
      m₂ (src + i) = mem (src + i) ∧ m₁ (src + i) = mem (src + i) := fun i hi => by
    have e1 : m₁ (src + i) = mem (src + i) := ho₁ _ (by omega)
    have e2 : m₂ (src + i) = mem (src + i) := (ho₂ _ (by omega)).trans e1
    have e3 : m₃ (src + i) = mem (src + i) := (ho₃ _ (by omega)).trans e2
    exact ⟨(ho₄ _ (by omega)).trans e3, e3, e2, e1⟩
  refine runs_ret_le (by eval_expr) ⟨hout, fun v' hv' hfv' => ?_⟩
    (by simp only [readValContract, copyWordsContract, Expr.size_reg, Expr.size_const,
      Expr.size_bin, argsSize_cons, argsSize_nil, atR]; omega)
  change PathEdgeAt mem src h K v' at hv'
  show PathEdgeAt m₅ dst h L v'
  cases v' with
  | none =>
    show m₅ dst = 0
    have := hc₁ 0 (by omega)
    simp only [Nat.add_zero] at this
    rw [ho₅ _ (by omega), ho₄ _ (by omega), ho₃ _ (by omega), ho₂ _ (by omega), this]
    exact hv'
  | some e =>
    obtain ⟨hh, hd, hg, hl, hfl, hdt⟩ := hv'
    obtain ⟨fg, fl, ff, fd⟩ := hfv'
    have hw01 : ∀ i < 2, m₅ (dst + i) = mem (src + i) := fun i hi => by
      rw [ho₅ _ (by omega), ho₄ _ (by omega), ho₃ _ (by omega), ho₂ _ (by omega), hc₁ i hi]
    refine ⟨by have := hw01 0 (by omega); simp only [Nat.add_zero] at this; rw [this]; exact hh,
      by rw [hw01 1 (by omega)]; exact hd, ?_, ?_, ?_, ?_⟩
    · exact pathIntAt_low hLK hg fg fun i hi => by
        rw [ho₅ _ (by omega), ho₄ _ (by omega), ho₃ _ (by omega), hc₂ i hi,
          show src + 2 + i = src + (2 + i) by omega]; exact (hsrc (2 + i) (by omega)).2.2.2
    · rw [show dst + 2 + L = dst + (2 + L) by omega]
      exact pathIntAt_low hLK (by rwa [show src + 2 + K = src + (2 + K) by omega] at hl) fl
        fun i hi => by
          rw [ho₅ _ (by omega), ho₄ _ (by omega), hc₃ i hi,
            show src + (2 + K) + i = src + (2 + K + i) by omega]
          exact (hsrc _ (by omega)).2.2.1
    · rw [show dst + 2 + 2 * L = dst + (2 + 2 * L) by omega]
      exact pathIntAt_low hLK (by rwa [show src + 2 + 2 * K = src + (2 + 2 * K) by omega] at hfl)
        ff fun i hi => by
          rw [ho₅ _ (by omega), hc₄ i hi,
            show src + (2 + 2 * K) + i = src + (2 + 2 * K + i) by omega]
          exact (hsrc _ (by omega)).2.1
    · rw [show dst + 2 + 3 * L = dst + (2 + 3 * L) by omega]
      exact pathIntAt_low hLK (by rwa [show src + 2 + 3 * K = src + (2 + 3 * K) by omega] at hdt)
        fd fun i hi => by
          rw [hc₅ i hi, show src + (2 + 3 * K) + i = src + (2 + 3 * K + i) by omega]
          exact (hsrc _ (by omega)).1

end MinCostFlow.LinkCut.Path
