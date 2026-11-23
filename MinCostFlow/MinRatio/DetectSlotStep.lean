module

public import MinCostFlow.MinRatio.DetectSlotReport
import WordRAM.Memory
import WordRAM.Tactic

/-!
# Preparing the report and reset for a ready slot

The proof of Theorem 5.1 (pages 29–30) reports each ready edge and
resets its detection account. Once the tree has supplied the edge
record, this fragment prepares the replacement value and appends the
original name. It leaves the replacement ready for the tree point
write.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Arguments are the two inverse tables, slot, cursor, resolved edge
record, threshold, limb count, and heap. -/
def detectSlotStepBody (reset report : ℕ) : Stmt :=
  .call 8 reset [.reg 4, .reg 5, .reg 6, .reg 7] ;;
  .call 9 report [.reg 0, .reg 1, .reg 2, .reg 3] ;;
  .ret (.reg 8)

/-- Prepare one reset payload and append the name to an existing report. -/
def detectSlotStepContract (w h report : ℕ) (written : List ℕ) (edge : PathEdgeValue)
    (threshold : ℤ) : Contract where
  pre args mem := ∃ names inv slot cursor src th L heap,
    args = [names, inv, slot, cursor, src, th, L, heap] ∧
    (detectResetContract w h edge threshold).pre [src, th, L, heap] mem ∧
    (detectSlotReportContract w report heap written).pre [names, inv, slot, cursor] mem
  post args mem ret mem' := ∃ names inv slot cursor src th L heap,
    args = [names, inv, slot, cursor, src, th, L, heap] ∧
    ret = heap + (2 + 4 * L) ∧
    ListAt mem' report (written ++ [mem (inv + mem (names + slot))]) ∧
    PathEdgeAt mem' heap h L (some { edge with detector := -threshold }) ∧
    (∀ x < heap, x ≠ cursor → mem' x = mem x) ∧ ZeroFrom mem' ret
  cost args _ := 87 * args.getD 6 0 + 144

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM

private theorem reset_record_frame {mem mem' : ℕ → ℕ} {base h L : ℕ} (edge : PathEdgeValue)
    (hr : PathEdgeAt mem base h L (some edge))
    (hf : ∀ x, base ≤ x → mem' x = mem x) :
    PathEdgeAt mem' base h L (some edge) := by
  exact hr.congr (fun x hx _ => hf x hx)

/-- A resolved ready record and its stored exact threshold suffice for
the combined append and replacement under the numeric bounds. -/
theorem detectSlotStep_pre_of_threshold_bound {w h L P E report names inv slot cursor src th heap : ℕ}
    {mem : ℕ → ℕ} (written : List ℕ) (edge : PathEdgeValue) (epsilon length : ℝ)
    (hw : 3 < 2 ^ w) (hsrc : src + (2 + 4 * L) ≤ heap) (hth : th + L ≤ heap)
    (hroom : heap + (2 + 4 * L) < 2 ^ w)
    (he : PathEdgeAt mem src h L (some edge))
    (ht : PathIntAt mem th h L (detectorThreshold P epsilon length))
    (heps : 0 < epsilon) (hepsU : epsilon ≤ (2 : ℝ)^E)
    (hlen : 1 / (2 : ℝ)^E ≤ length) (hwidth : P + 2 * E + 3 ≤ h * L)
    (hz : ZeroFrom mem heap)
    (hreport : (detectSlotReportContract w report heap written).pre [names, inv, slot, cursor] mem) :
    (detectSlotStepContract w h report written edge (detectorThreshold P epsilon length)).pre
      [names, inv, slot, cursor, src, th, L, heap] mem :=
  ⟨names, inv, slot, cursor, src, th, L, heap, rfl,
    detectReset_pre_of_threshold_bound edge epsilon length hw hsrc hth hroom he ht
      heps hepsU hlen hwidth hz, hreport⟩

/-- The combined step uses `2 + 4 * L` new words and at most
`87 * L + 144` steps. -/
theorem detectSlotStep_meetsContract {w h entry reset emit report : ℕ} {p : Program}
    (written : List ℕ) (edge : PathEdgeValue) (threshold : ℤ)
    (hp : p.HasAt entry [detectSlotStepBody reset emit])
    (hr : MeetsContract w p reset (detectResetContract w h edge threshold))
    (he : ∀ heap, MeetsContract w p emit (detectSlotReportContract w report heap written)) :
    MeetsContract w p entry (detectSlotStepContract w h report written edge threshold) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨names, inv, slot, cursor, src, th, L, heap, rfl, hrpre, hepre⟩ := hpre
  obtain ⟨names', inv', slot', cursor', heargs, hcursor, hname, hinv, hlt, hheap, hword, hlist, _⟩ := hepre
  simp only [List.cons.injEq, and_true] at heargs
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heargs
  have hn := hwords names (by simp)
  have hi := hwords inv (by simp)
  have hs := hwords slot (by simp)
  have hc := hwords cursor (by simp)
  have hsrc := hwords src (by simp)
  have hth := hwords th (by simp)
  have hL := hwords L (by simp)
  have hbound : heap + (2 + 4 * L) < 2 ^ w := by
    obtain ⟨a, b, c, d, hab, _, _, _, hroom, _⟩ := hrpre
    simp only [List.cons.injEq, and_true] at hab
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hab
    exact hroom
  apply runs_start_le
  unfold detectSlotStepBody
  refine runs_seq_call_le hr (vs := [src, th, L, heap]) (by eval_expr) (by wram_words) hrpre ?_
  intro top mem₁ pos₁ hp₁
  obtain ⟨a, b, c, d, hargs, htop, hpayload, hframe, hz₁⟩ := hp₁
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hargs
  change (∀ x < heap, mem₁ x = mem x) at hframe
  have htopw : top < 2 ^ w := by omega
  have hword₁ : mem₁ (names + slot) = mem (names + slot) := hframe _ (by omega)
  have hword₂ : mem₁ (inv + mem₁ (names + slot)) = mem (inv + mem (names + slot)) := by
    rw [hword₁]
    exact hframe _ (by omega)
  have hlist₁ : ListAt mem₁ report written := hlist.congr fun i _ hi => hframe _ (by omega)
  refine runs_seq_call_le (he top) (vs := [names, inv, slot, cursor])
    (by eval_expr) (by wram_words) ?_ ?_
  · refine ⟨names, inv, slot, cursor, rfl, hcursor, hname, ?_, by omega, htopw, ?_, hlist₁, hz₁⟩
    · change inv + mem₁ (names + slot) < cursor
      rwa [hword₁]
    · change mem₁ (inv + mem₁ (names + slot)) < 2 ^ w
      rwa [hword₂]
  · intro ignored mem₂ pos₂ hp₂
    obtain ⟨_, hlist₂, hframe₂, hz₂⟩ := hp₂
    change ListAt mem₂ report (written ++ [mem₁ (inv + mem₁ (names + slot))]) at hlist₂
    rw [hword₂] at hlist₂
    change ∀ x ≠ cursor, mem₂ x = mem₁ x at hframe₂
    refine runs_ret_le (v := top) (by eval_expr) ?_ ?_
    · exact ⟨names, inv, slot, cursor, src, th, L, heap, rfl, htop, hlist₂,
        reset_record_frame _ hpayload (fun x hx => hframe₂ x (by omega)),
        fun x hx hne => (hframe₂ x hne).trans (hframe x hx), hz₂⟩
    · simp only [detectSlotStepContract, detectResetContract, detectSlotReportContract,
        List.getD_cons_zero, List.getD_cons_succ, Expr.size_reg, argsSize_cons, argsSize_nil]
      omega

end MinCostFlow.MinRatio
