module

public import MinCostFlow.LinkCut.Path.ReadVal

/-!
# Copying a path summary out in fewer limbs

A path summary query returns the summary of the exposed path in the interface width `L`, while
the node record keeps it in `K ≥ L` limbs. `readSumBody` copies the low `L` limbs of the two
sums, the detector flag, and the low `L` limbs of the detector. When the numbers fit in `L`
limbs this is exact (`pathIntAt_low`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Path

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio

/-- `readSum [src, dst, K, L]`: copy the `K`-limb summary at `src` to an `L`-limb one at
`dst`. -/
def readSumBody (copyProc : ℕ) : Stmt :=
  .call 4 copyProc [.reg 0, .reg 1, .reg 3] ;;
  .call 4 copyProc [.bin .add (.reg 0) (.reg 2), .bin .add (.reg 1) (.reg 3), .reg 3] ;;
  .call 4 copyProc [atR 0 2 0 2, atR 1 3 0 2, .const 1] ;;
  .call 4 copyProc [atR 0 2 1 2, atR 1 3 1 2, .reg 3] ;;
  .ret (.const 0)

theorem readSumBody_noRand (b : ℕ) : (readSumBody b).NoRand := by
  simp [readSumBody, Stmt.NoRand]

/-- The contract of `readSumBody`. The two blocks do not overlap. -/
def readSumContract (w h K L : ℕ) : Contract where
  pre args mem := ∃ src dst, args = [src, dst, K, L] ∧ 1 < 2 ^ w ∧ L ≤ K ∧
    src + (3 * K + 1) < 2 ^ w ∧ dst + (3 * L + 1) < 2 ^ w ∧
    (src + (3 * K + 1) ≤ dst ∨ dst + (3 * L + 1) ≤ src) ∧
    ∃ s, PathSummaryAt mem src h K s ∧ PathSummaryFits h L s
  post args mem _ mem' :=
    (∀ y, ¬ (args.getD 1 0 ≤ y ∧ y < args.getD 1 0 + (3 * L + 1)) → mem' y = mem y) ∧
    ∀ s, PathSummaryAt mem (args.getD 0 0) h K s → PathSummaryFits h L s →
      PathSummaryAt mem' (args.getD 1 0) h L s
  cost _ _ := 60 * L + 200

theorem readSum_meetsContract {w h K L f copyProc : ℕ} {p : Program}
    (hb : p.procs[f]? = some (readSumBody copyProc))
    (hcopy : MeetsContract w p copyProc (copyWordsContract w)) :
    MeetsContract w p f (readSumContract w h K L) := by
  apply meetsContract_of_runs hb
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨src, dst, rfl, hw, hLK, hsw, hdw, hdis, s, hs, hfs⟩
  apply runs_start_le
  unfold readSumBody
  refine runs_seq_call_le hcopy (vs := [src, dst, L]) (by eval_expr) (by
      intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨_, _, _, rfl, hw, by omega, by omega, by omega⟩ ?_
  rintro v₁ m₁ pos₁ ⟨s₁, d₁, l₁, heq₁, -, hc₁, ho₁⟩
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl⟩ := heq₁
  change ∀ i < L, m₁ (dst + i) = mem (src + i) at hc₁
  change ∀ y, y < dst ∨ dst + L ≤ y → m₁ y = mem y at ho₁
  refine runs_seq_call_le hcopy (vs := [src + K, dst + L, L]) (by eval_expr) (by
      intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨_, _, _, rfl, hw, by omega, by omega, by omega⟩ ?_
  rintro v₂ m₂ pos₂ ⟨s₂, d₂, l₂, heq₂, -, hc₂, ho₂⟩
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl⟩ := heq₂
  change ∀ i < L, m₂ (dst + L + i) = m₁ (src + K + i) at hc₂
  change ∀ y, y < dst + L ∨ dst + L + L ≤ y → m₂ y = m₁ y at ho₂
  refine runs_seq_call_le hcopy (vs := [src + (0 + 2 * K), dst + (0 + 2 * L), 1])
    (by eval_expr) (by
      intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨_, _, _, rfl, hw, by omega, by omega, by omega⟩ ?_
  rintro v₃ m₃ pos₃ ⟨s₃, d₃, l₃, heq₃, -, hc₃, ho₃⟩
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl⟩ := heq₃
  change ∀ i < 1, m₃ (dst + (0 + 2 * L) + i) = m₂ (src + (0 + 2 * K) + i) at hc₃
  change ∀ y, y < dst + (0 + 2 * L) ∨ dst + (0 + 2 * L) + 1 ≤ y → m₃ y = m₂ y at ho₃
  refine runs_seq_call_le hcopy (vs := [src + (1 + 2 * K), dst + (1 + 2 * L), L])
    (by eval_expr) (by
      intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨_, _, _, rfl, hw, by omega, by omega, by omega⟩ ?_
  rintro v₄ m₄ pos₄ ⟨s₄, d₄, l₄, heq₄, -, hc₄, ho₄⟩
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl⟩ := heq₄
  change ∀ i < L, m₄ (dst + (1 + 2 * L) + i) = m₃ (src + (1 + 2 * K) + i) at hc₄
  change ∀ y, y < dst + (1 + 2 * L) ∨ dst + (1 + 2 * L) + L ≤ y → m₄ y = m₃ y at ho₄
  have hout : ∀ y, ¬ (dst ≤ y ∧ y < dst + (3 * L + 1)) → m₄ y = mem y := fun y hy => by
    rw [ho₄ y (by omega), ho₃ y (by omega), ho₂ y (by omega), ho₁ y (by omega)]
  have hsrc : ∀ i < 3 * K + 1, m₃ (src + i) = mem (src + i) ∧ m₂ (src + i) = mem (src + i) ∧
      m₁ (src + i) = mem (src + i) := fun i hi => by
    have e1 : m₁ (src + i) = mem (src + i) := ho₁ _ (by omega)
    have e2 : m₂ (src + i) = mem (src + i) := (ho₂ _ (by omega)).trans e1
    exact ⟨(ho₃ _ (by omega)).trans e2, e2, e1⟩
  refine runs_ret_le (by eval_expr) ⟨hout, fun s' hs' hfs' => ?_⟩
    (by simp only [readSumContract, copyWordsContract, Expr.size_reg, Expr.size_const,
      Expr.size_bin, argsSize_cons, argsSize_nil, atR]; omega)
  change PathSummaryAt mem src h K s' at hs'
  show PathSummaryAt m₄ dst h L s'
  obtain ⟨hg, hl, hd⟩ := hs'
  obtain ⟨fg, fl, fd⟩ := hfs'
  have hflag : m₄ (dst + 2 * L) = mem (src + 2 * K) := by
    have := hc₃ 0 (by omega)
    simp only [Nat.zero_add, Nat.add_zero] at this
    rw [ho₄ _ (by omega), this, ho₂ _ (by omega), ho₁ _ (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · exact pathIntAt_low hLK hg fg fun i hi => by
      rw [ho₄ _ (by omega), ho₃ _ (by omega), ho₂ _ (by omega), hc₁ i hi]
  · exact pathIntAt_low hLK hl fl fun i hi => by
      rw [ho₄ _ (by omega), ho₃ _ (by omega), hc₂ i hi,
        show src + K + i = src + (K + i) by omega]
      exact (hsrc _ (by omega)).2.2
  · revert hd fd
    cases s'.detector with
    | none =>
      intro hd _
      show m₄ (dst + 2 * L) = 0
      rw [hflag]; exact hd
    | some z =>
      rintro ⟨hd1, hdz⟩ fz
      refine ⟨by rw [hflag]; exact hd1, ?_⟩
      exact pathIntAt_low hLK hdz fz fun i hi => by
        rw [show dst + 2 * L + 1 + i = dst + (1 + 2 * L) + i by omega, hc₄ i hi,
          show src + (1 + 2 * K) + i = src + (2 * K + 1 + i) by omega,
          show src + 2 * K + 1 + i = src + (2 * K + 1 + i) by omega]
        exact (hsrc _ (by omega)).1

end MinCostFlow.LinkCut.Path
