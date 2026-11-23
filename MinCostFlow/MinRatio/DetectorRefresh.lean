module

public import MinCostFlow.MinRatio.DetectorThreshold
public import MinCostFlow.MinRatio.PathPayloadLayout
public import MinCostFlow.Num.Subtract
import WordRAM.Tactic

/-!
# Updating an edge's detection residual after a length change

The proof of Theorem 5.1 (pages 29–30) keeps accumulated absolute flow
and tests it against a threshold that depends on the current length.
When a length changes, the old account stays in place. Adding the
difference of the thresholds gives its exact new residual.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Arguments are the residual, old threshold, new threshold, limb count,
and heap. The new residual is the last block of the allocation. -/
def detectorRefreshBody (subtract add : ℕ) : Stmt :=
  .call 5 subtract [.reg 1, .reg 2, .reg 3, .reg 4] ;;
  .call 6 add [.reg 0, .bin .add (.reg 4) (.reg 3), .reg 3, .reg 5] ;;
  .ret (.reg 6)

/-- Change the threshold contribution in a stored residual. Only the
final result needs to fit the signed range. -/
def detectorRefreshContract (w h : ℕ) (residual oldThreshold newThreshold : ℤ) : Contract where
  pre args mem := ∃ r old new L heap, args = [r, old, new, L, heap] ∧
    r + L ≤ heap ∧ old + L ≤ heap ∧ new + L ≤ heap ∧
    PathIntAt mem r h L residual ∧ PathIntAt mem old h L oldThreshold ∧
    PathIntAt mem new h L newThreshold ∧ Num.Fits h L (residual + (oldThreshold - newThreshold)) ∧
    ZeroFrom mem heap ∧ heap + 3 * L < 2 ^ w
  post args mem ret mem' := ∃ r old new L heap, args = [r, old, new, L, heap] ∧
    ret = heap + 3 * L ∧
    PathIntAt mem' (heap + 2 * L) h L (residual + (oldThreshold - newThreshold)) ∧
    (∀ x < heap, mem' x = mem x) ∧ ZeroFrom mem' ret
  cost args _ := 112 * args.getD 3 0 + 76

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- The threshold adjustment costs `112 * L + 76` steps or fewer. The
two arithmetic calls can wrap their intermediate results because only
the final residual is observed. -/
theorem detectorRefresh_meetsContract {w h entry subtract add : ℕ} {p : Program}
    (residual oldThreshold newThreshold : ℤ)
    (hp : p.HasAt entry [detectorRefreshBody subtract add])
    (hs : MeetsContract w p subtract (Num.subtractContract w h))
    (ha : MeetsContract w p add (Num.addContract w h)) :
    MeetsContract w p entry (detectorRefreshContract w h residual oldThreshold newThreshold) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨r, old, new, L, heap, rfl, hr, ho, hn, hres, hold, hnew, hfit, hz, hroom⟩ := hpre
  have hrw := hwords r (by simp)
  have how := hwords old (by simp)
  have hnw := hwords new (by simp)
  have hLw := hwords L (by simp)
  have hhw := hwords heap (by simp)
  have hmidw : heap + L < 2 ^ w := by omega
  apply runs_start_le
  unfold detectorRefreshBody
  refine runs_seq_call_le hs (vs := [old, new, L, heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨old, new, L, heap, rfl, ho, hn, hold.1, hnew.1⟩, hz, by
      change heap + 2 * L < 2 ^ w
      omega⟩
  · intro ptr mem₁ pos₁ hpost
    obtain ⟨hptr, _, _, hf, hz₁, hδvalid, hδ⟩ := hpost
    change ptr = heap + 2 * L at hptr
    change (∀ x < heap, mem₁ x = mem x) at hf
    have hptrw : ptr < 2 ^ w := by omega
    have hres₁ := hres.congr (mem' := mem₁) (fun i hi => hf _ (by omega))
    change Num.intVal mem₁ (heap + L) h L =
      Num.wrap h L (Num.intVal mem old h L - Num.intVal mem new h L) at hδ
    rw [hold.2, hnew.2] at hδ
    refine runs_seq_call_le ha (vs := [r, heap + L, L, ptr]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨r, heap + L, L, ptr, rfl,
        ⟨⟨r, heap + L, L, 0, ptr, rfl, by omega, by omega, by decide, hres₁.1, hδvalid⟩,
          hz₁, by change ptr + L < 2 ^ w; omega⟩⟩
    · intro ret mem₂ pos₂ hp₂
      obtain ⟨hret, _, _, hf₂, hz₂, hdigits⟩ := hp₂
      change ret = ptr + L at hret
      change (∀ x < ptr, mem₂ x = mem₁ x) at hf₂
      change ListAt mem₂ ptr (Num.digits h L
        (Num.unsignedVal mem₁ r h L + Num.unsignedVal mem₁ (heap + L) h L + 0)) at hdigits
      obtain ⟨hv, he⟩ := Num.addCarry_value hdigits
      rw [hres₁.2, hδ, Int.natCast_zero, add_zero, Num.wrap_add_wrap, Num.wrap_of_fits hfit] at he
      refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · exact ⟨r, old, new, L, heap, rfl, by change ret = heap + 3 * L; omega, hptr ▸ ⟨hv, he⟩,
          fun x hx => (hf₂ x (by omega)).trans (hf x hx), hz₂⟩
      · simp only [detectorRefreshContract, Num.subtractContract, Num.addContract, heapContract,
          List.getD_cons_zero, List.getD_cons_succ, Expr.size_bin, Expr.size_reg, argsSize_cons,
          argsSize_nil]
        omega

/-- Reading the new block after a length refresh gives the same account
with the new threshold, as required by Algorithm 2 (page 29). -/
theorem detectorRefresh_account {w h P L r old new heap ret : ℕ} {mem mem' : ℕ → ℕ}
    (epsilon oldLength newLength : ℝ) (account : ℤ)
    (hout : (detectorRefreshContract w h (account - detectorThreshold P epsilon oldLength)
      (detectorThreshold P epsilon oldLength) (detectorThreshold P epsilon newLength)).post
      [r, old, new, L, heap] mem ret mem') :
    PathIntAt mem' (heap + 2 * L) h L (account - detectorThreshold P epsilon newLength) := by
  obtain ⟨a, b, c, limbs, dst, hargs, _, hv, _, _⟩ := hout
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
  rwa [detectorThreshold_refresh P epsilon oldLength newLength account] at hv

end MinCostFlow.MinRatio
