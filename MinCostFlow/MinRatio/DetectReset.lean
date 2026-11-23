module

public import MinCostFlow.MinRatio.PathPayloadLayout
public import MinCostFlow.Num.Negate
public import WordRAM.CopyWords
import WordRAM.Tactic

public import MinCostFlow.MinRatio.DetectorThreshold

/-!
# Preparing the replacement edge payload after Detect

The reporting loop in the proof of Theorem 5.1 (pages 29–30) resets
the account of each reported edge. Its new residual is the negative
of the stored integer threshold. This procedure copies the other
fields of the resolved edge record and writes that negative threshold.
It supplies the replacement record for a tree point write.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Arguments are the resolved record, stored threshold, limb count,
and heap. The returned pointer follows the replacement record. -/
def detectResetBody (copy negate : ℕ) : Stmt :=
  .assign 4 (.bin .add (.const 2) (.bin .mul (.const 3) (.reg 2))) ;;
  .assign 5 (.bin .add (.reg 3) (.reg 4)) ;;
  .call 6 copy [.reg 0, .reg 3, .reg 4] ;;
  .call 6 negate [.reg 1, .reg 2, .reg 5] ;;
  .ret (.reg 6)

/-- Replace only the detector field by the negative of a stored
threshold. The caller supplies the exact threshold and range proofs. -/
def detectResetContract (w h : ℕ) (edge : PathEdgeValue) (threshold : ℤ) : Contract where
  pre args mem := ∃ src th L heap, args = [src, th, L, heap] ∧ 3 < 2 ^ w ∧
    src + (2 + 4 * L) ≤ heap ∧ th + L ≤ heap ∧ heap + (2 + 4 * L) < 2 ^ w ∧
    PathEdgeAt mem src h L (some edge) ∧ PathIntAt mem th h L threshold ∧
    Num.Fits h L (-threshold) ∧ ZeroFrom mem heap
  post args mem ret mem' := ∃ src th L heap, args = [src, th, L, heap] ∧
    ret = heap + (2 + 4 * L) ∧ PathEdgeAt mem' heap h L (some { edge with detector := -threshold }) ∧
    (∀ a < heap, mem' a = mem a) ∧ ZeroFrom mem' ret
  cost args _ := 87 * args.getD 2 0 + 96

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM

private theorem path_prefix_of_copy {ma mb : ℕ → ℕ} {src dst h L : ℕ}
    (edge : PathEdgeValue) (threshold : ℤ)
    (ha : PathEdgeAt ma src h L (some edge))
    (he : ∀ i < 2 + 3 * L, mb (dst + i) = ma (src + i))
    (hd : PathIntAt mb (dst + 2 + 3 * L) h L (-threshold)) :
    PathEdgeAt mb dst h L (some { edge with detector := -threshold }) := by
  rcases ha with ⟨htag, hdir, hg, hl, hf, _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hd⟩
  · have h0 : mb dst = ma src := by simpa only [Nat.add_zero] using he 0 (by omega)
    exact h0.trans htag
  · exact (he 1 (by omega)).trans hdir
  · refine hg.congr ?_
    intro i hi
    simpa only [Nat.add_assoc] using he (2 + i) (by omega)
  · refine hl.congr ?_
    intro i hi
    simpa only [Nat.add_assoc] using he (2 + L + i) (by omega)
  · refine hf.congr ?_
    intro i hi
    simpa only [Nat.add_assoc] using he (2 + 2 * L + i) (by omega)

/-- The replacement payload uses `2 + 4 * L` new words and costs at most
`87 * L + 96` steps for every random tape. -/
theorem detectReset_meetsContract {w h entry copy negate : ℕ} {p : Program}
    (edge : PathEdgeValue) (threshold : ℤ)
    (hp : p.HasAt entry [detectResetBody copy negate])
    (hc : MeetsContract w p copy (copyWordsContract w))
    (hn : MeetsContract w p negate (Num.negateContract w h)) :
    MeetsContract w p entry (detectResetContract w h edge threshold) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨src, th, L, heap, rfl, hw, hs, ht, hh, he, hth, hfit, hz⟩ := hpre
  let prefixWords := 2 + 3 * L
  let detectorPtr := heap + prefixWords
  have hprefix : prefixWords = 2 + 3 * L := rfl
  have hdetector : detectorPtr = heap + prefixWords := rfl
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have h3L : 3 * L < 2 ^ w := by omega
  have hsw : src + prefixWords ≤ heap := by omega
  have hheapw : heap < 2 ^ w := by omega
  have hsrcw : src < 2 ^ w := by omega
  have hthw : th < 2 ^ w := by omega
  have hLw : L < 2 ^ w := by omega
  have hpw : prefixWords < 2 ^ w := by omega
  have hdw : detectorPtr < 2 ^ w := by omega
  have hfinal : detectorPtr + L = heap + (2 + 4 * L) := by omega
  have hfinalw : detectorPtr + L < 2 ^ w := by omega
  have hcWords : ∀ x ∈ [src, heap, prefixWords], x < 2 ^ w := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hsrcw, hheapw, hpw⟩
  have hnWords : ∀ x ∈ [th, L, detectorPtr], x < 2 ^ w := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hthw, hLw, hdw⟩
  apply runs_start_le
  unfold detectResetBody
  refine runs_seq_assign_le (v := prefixWords) (by eval_expr) ?_
  refine runs_seq_assign_le (v := detectorPtr) (by eval_expr) ?_
  refine runs_seq_call_le hc (vs := [src, heap, prefixWords]) (by eval_expr) hcWords ?_ ?_
  · exact ⟨src, heap, prefixWords, rfl, h1, by omega, by omega, Or.inr hsw⟩
  · intro v₁ mem₁ pos₁ hp₁
    obtain ⟨source, target, len, hargs, _, hcopy, hframe⟩ := hp₁
    simp only [List.cons.injEq, and_true] at hargs
    rcases hargs with ⟨rfl, rfl, rfl⟩
    have hbelow : ∀ a < heap, mem₁ a = mem a := fun a ha => hframe a (Or.inl ha)
    have hz₁ : ZeroFrom mem₁ detectorPtr := by
      intro a ha
      exact (hframe a (Or.inr ha)).trans (hz a (by omega))
    have hth₁ : PathIntAt mem₁ th h L threshold :=
      hth.congr fun i hi => hbelow _ (by omega)
    refine runs_seq_call_le hn (vs := [th, L, detectorPtr]) (by eval_expr) hnWords ?_ ?_
    · exact ⟨th, L, detectorPtr, rfl,
        ⟨⟨th, L, 1, detectorPtr, rfl, by omega, le_rfl, hth₁.1⟩, hz₁, hfinalw⟩⟩
    · intro v₂ mem₂ pos₂ hp₂
      obtain ⟨hret, _, _, hframe₂, hz₂, hdigits⟩ := hp₂
      change v₂ = detectorPtr + L at hret
      change (∀ a < detectorPtr, mem₂ a = mem₁ a) at hframe₂
      obtain ⟨hdvalid, hdval⟩ := Num.negateCarry_value_one hth₁.1 hdigits
      rw [hth₁.2, Num.wrap_of_fits hfit] at hdval
      have hdet : PathIntAt mem₂ (heap + 2 + 3 * L) h L (-threshold) := by
        have heq : detectorPtr = heap + 2 + 3 * L := by omega
        exact heq ▸ (⟨hdvalid, hdval⟩ : PathIntAt mem₂ detectorPtr h L (-threshold))
      have hprefix₂ : ∀ i < 2 + 3 * L, mem₂ (heap + i) = mem (src + i) := by
        intro i hi
        exact (hframe₂ _ (by omega)).trans (hcopy i hi)
      refine runs_ret_le (v := v₂) (by eval_expr) ?_ ?_
      · exact ⟨src, th, L, heap, rfl, hret.trans hfinal,
          path_prefix_of_copy edge threshold he hprefix₂ hdet,
          fun a ha => (hframe₂ a (by omega)).trans (hbelow a ha), hz₂⟩
      · change _ ≤ 87 * L + 96
        simp only [Expr.size_const, Expr.size_reg, Expr.size_bin, argsSize_cons, argsSize_nil,
          copyWordsContract, Num.negateContract, List.getD_cons_succ, List.getD_cons_zero]
        omega

/-- The signed range premise of the Detect replacement follows from
the length and epsilon bounds when the input stores the exact threshold. -/
theorem detectReset_pre_of_threshold_bound {w h L P E src th heap : ℕ}
    {mem : ℕ → ℕ} (edge : PathEdgeValue) (epsilon length : ℝ)
    (hw : 3 < 2 ^ w) (hsrc : src + (2 + 4 * L) ≤ heap) (hth : th + L ≤ heap)
    (hroom : heap + (2 + 4 * L) < 2 ^ w)
    (he : PathEdgeAt mem src h L (some edge))
    (ht : PathIntAt mem th h L (detectorThreshold P epsilon length))
    (heps : 0 < epsilon) (hepsU : epsilon ≤ (2 : ℝ)^E)
    (hlen : 1 / (2 : ℝ)^E ≤ length) (hwidth : P + 2 * E + 3 ≤ h * L)
    (hz : ZeroFrom mem heap) :
    (detectResetContract w h edge (detectorThreshold P epsilon length)).pre [src, th, L, heap] mem :=
  ⟨src, th, L, heap, rfl, hw, hsrc, hth, hroom, he, ht,
    detectorThreshold_reset_fits epsilon length heps hepsU hlen hwidth, hz⟩

end MinCostFlow.MinRatio
