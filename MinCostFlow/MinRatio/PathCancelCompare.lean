module

public import MinCostFlow.MinRatio.PathPayloadLayout
public import MinCostFlow.Num.Add
public import MinCostFlow.Num.Less
public import MinCostFlow.Basic.Forest
import MinCostFlow.MinRatio.PathIntAdd
import MinCostFlow.MinRatio.PathCancellationAccounting
import WordRAM.Tactic

/-!
# Comparing the lengths before and after a destination swap

Algorithm 2 (page 29) can detect a cancelling pair of tree paths by
comparing the two weighted length sums. This fragment adds the two
pairs of stored numerators and returns their exact comparison.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Arguments are the two original lengths, the two swapped lengths,
the limb count, and the scratch heap. -/
def pathCancelCompareBody (add less : ℕ) : Stmt :=
  .call 6 add [.reg 0, .reg 1, .reg 4, .reg 5] ;;
  .call 7 add [.reg 2, .reg 3, .reg 4, .reg 6] ;;
  .call 8 less [.reg 6, .reg 5, .reg 4] ;;
  .ret (.reg 8)

/-- Compare the length sums with two scratch blocks. -/
def pathCancelCompareContract (w h : ℕ) (ab cd ad cb : ℤ) : Contract where
  pre args mem := ∃ a b c d L heap, args = [a, b, c, d, L, heap] ∧ 1 < 2 ^ w ∧
    a + L ≤ heap ∧ b + L ≤ heap ∧ c + L ≤ heap ∧ d + L ≤ heap ∧
    PathIntAt mem a h L ab ∧ PathIntAt mem b h L cd ∧
    PathIntAt mem c h L ad ∧ PathIntAt mem d h L cb ∧
    Num.Fits h L (ab + cd) ∧ Num.Fits h L (ad + cb) ∧
    ZeroFrom mem heap ∧ heap + 2 * L < 2 ^ w
  post args mem ret mem' := ret = (if ad + cb < ab + cd then 1 else 0) ∧
    (∀ x < heapArg args, mem' x = mem x) ∧ ZeroFrom mem' (heapArg args + 2 * args.getD 4 0)
  cost args _ := 117 * args.getD 4 0 + 110

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Comparing the sums costs at most `117 * L + 110` steps. -/
theorem pathCancelCompare_meetsContract {w h entry add less : ℕ} {p : Program}
    (ab cd ad cb : ℤ) (hp : p.HasAt entry [pathCancelCompareBody add less])
    (ha : MeetsContract w p add (Num.addContract w h))
    (hl : MeetsContract w p less (Num.lessContract w h)) :
    MeetsContract w p entry (pathCancelCompareContract w h ab cd ad cb) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a, b, c, d, L, heap, rfl, hw, ha₀, hb₀, hc₀, hd₀, hA, hB, hC, hD, hf₁, hf₂, hz, hroom⟩ := hpre
  have haw := hwords a (by simp)
  have hbw := hwords b (by simp)
  have hcw := hwords c (by simp)
  have hdw := hwords d (by simp)
  have hlw := hwords L (by simp)
  have hhw := hwords heap (by simp)
  apply runs_start_le
  unfold pathCancelCompareBody
  refine runs_seq_call_le ha (vs := [a, b, L, heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact addPathInt_pre hA hB ha₀ hb₀ hz (by omega)
  · intro mid mem₁ pos₁ hp₁
    obtain ⟨hmid, hframe₁, hz₁, hs₁⟩ := addPathInt_post hA hB hf₁ hp₁
    have hmidw : mid < 2 ^ w := by omega
    have hC₁ := hC.congr (mem' := mem₁) (fun i hi => hframe₁ _ (by omega))
    have hD₁ := hD.congr (mem' := mem₁) (fun i hi => hframe₁ _ (by omega))
    refine runs_seq_call_le ha (vs := [c, d, L, mid]) (by eval_expr) (by wram_words) ?_ ?_
    · exact addPathInt_pre hC₁ hD₁ (by omega) (by omega) hz₁ (by omega)
    · intro top mem₂ pos₂ hp₂
      obtain ⟨htop, hframe₂, hz₂, hs₂⟩ := addPathInt_post hC₁ hD₁ hf₂ hp₂
      have hs₁' := hs₁.congr (mem' := mem₂) (fun i hi => hframe₂ _ (by omega))
      refine runs_seq_call_le hl (vs := [mid, heap, L]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨mid, heap, L, rfl, by omega, by omega, hs₂.1, hs₁'.1⟩
      · intro ret mem₃ pos₃ hp₃
        obtain ⟨hmem, hret⟩ := hp₃
        change mem₃ = mem₂ at hmem
        subst mem₃
        change ret = (if Num.intVal mem₂ mid h L < Num.intVal mem₂ heap h L then 1 else 0) at hret
        rw [hs₂.2, hs₁'.2] at hret
        have hretw : ret < 2 ^ w := by
          rw [hret]
          split <;> omega
        refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
        · refine ⟨hret, fun x hx => (hframe₂ x (by change x < heap at hx; omega)).trans (hframe₁ x hx), ?_⟩
          intro x hx
          change heap + 2 * L ≤ x at hx
          exact hz₂ x (by omega)
        · simp only [pathCancelCompareContract, Num.addContract, Num.lessContract,
            List.getD_cons_zero, List.getD_cons_succ, Expr.size_reg, argsSize_cons, argsSize_nil]
          omega

/-- When the supplied blocks are the four path lengths at one
precision, the comparison bit detects exactly an opposite traversal. -/
theorem pathCancelCompare_opposite {F : MGraph} (hF : F.IsForest)
    (length : ℕ → ℝ) (hℓ : ∀ e ∈ F.E, 0 < length e)
    {a b c d P w h ret : ℕ} {ab cd ad cb : ℤ}
    {args : List ℕ} {mem mem' : ℕ → ℕ}
    (hab : F.Connected a b) (hac : F.Connected a c) (hcd : F.Connected c d)
    (hAB : walkLength length (F.forestPath a b) = (ab : ℝ) / (2 : ℝ) ^ P)
    (hCD : walkLength length (F.forestPath c d) = (cd : ℝ) / (2 : ℝ) ^ P)
    (hAD : walkLength length (F.forestPath a d) = (ad : ℝ) / (2 : ℝ) ^ P)
    (hCB : walkLength length (F.forestPath c b) = (cb : ℝ) / (2 : ℝ) ^ P)
    (hout : (pathCancelCompareContract w h ab cd ad cb).post args mem ret mem') :
    ret = 1 ↔ ∃ x ∈ F.forestPath a b, (x.1, !x.2) ∈ F.forestPath c d := by
  have hp : 0 < (2 : ℝ) ^ P := pow_pos (zero_lt_two : (0 : ℝ) < 2) _
  have htest := pathCancel_weighted_swap_iff hF length hℓ hab hac hcd
  rw [hAB, hCD, hAD, hCB, ← add_div, ← add_div, div_lt_div_iff_of_pos_right hp,
    ← Int.cast_add, ← Int.cast_add, Int.cast_lt] at htest
  rw [hout.1, ← htest]
  by_cases ht : ad + cb < ab + cd <;> simp [ht]

end MinCostFlow.MinRatio
