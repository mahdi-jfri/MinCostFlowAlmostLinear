module

public import MinCostFlow.IPM.Machine.MinRatioContract
public import MinCostFlow.MinRatio.PathPayloadLayout
public import MinCostFlow.Num.FixedDivide
public import MinCostFlow.Num.Multiply
import MinCostFlow.MinRatio.PathFlowNormalization
import WordRAM.Tactic

/-!
# Computing the path multiplier and actual normalization

Algorithm 2 (page 29) divides the requested step by the direction's
gradient sum. Given the positive magnitude of that sum, the machine
computes a floor quotient at the flow precision. It then multiplies
the stored quotient by that same gradient magnitude without truncating
the product. The IPM receives the actual normalization at double precision.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine

/-- Arguments are request, gradient magnitude, limbs, precision, and heap. -/
def pathNormalizationBody (divide multiply : ℕ) : Stmt :=
  .call 5 divide [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4] ;;
  .call 6 multiply [.bin .sub (.reg 5) (.reg 2), .reg 1, .reg 2, .reg 5] ;;
  .ret (.reg 6)

/-- Integer numerator of the stored multiplier. -/
def pathMultiplier (P : ℕ) (request magnitude : ℤ) : ℤ :=
  Num.floorDiv (request * (2 : ℤ) ^ P) magnitude

/-- The multiplier ends the divider allocation, and the exact product
ends the multiplier's workspace. Both have their declared precision. -/
noncomputable def pathNormalizationContract (w h : ℕ) (request magnitude : ℤ) : Contract where
  pre args mem := ∃ a d L P heap, args = [a, d, L, P, heap] ∧ h ∣ P ∧
    a + L ≤ heap ∧ d + L ≤ heap ∧ 0 < magnitude ∧
    PathIntAt mem a h L request ∧ PathIntAt mem d h L magnitude ∧
    Num.Fits h L (pathMultiplier P request magnitude) ∧
    ZeroFrom mem heap ∧ heap + Num.fixedDivideSpace L + 6 * L < 2 ^ w
  post args mem ret mem' := ∃ a d L P heap, args = [a, d, L, P, heap] ∧
    ret = heap + Num.fixedDivideSpace L + 6 * L ∧
    PathIntAt mem' (heap + Num.fixedDivideSpace L - L) h L (pathMultiplier P request magnitude) ∧
    PathIntAt mem' (ret - 2 * L) h (2 * L) (pathMultiplier P request magnitude * magnitude) ∧
    (∀ x < heap, mem' x = mem x) ∧ ZeroFrom mem' ret
  cost args _ := 2852 * (args.getD 2 0) ^ 2 + 3022 * args.getD 2 0 + 830

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine

/-- The two calls compute the rounded multiplier and exact product in
quadratic time in the number of limbs. -/
theorem pathNormalization_meetsContract {w h entry divide multiply : ℕ} {p : Program}
    (request magnitude : ℤ)
    (hp : p.HasAt entry [pathNormalizationBody divide multiply])
    (hd : MeetsContract w p divide (Num.fixedDivideContract w h))
    (hm : MeetsContract w p multiply (Num.multiplyContract w h)) :
    MeetsContract w p entry (pathNormalizationContract w h request magnitude) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a, d, L, P, heap, rfl, hP, ha, hb, hpos, hva, hvd, hfit, hz, hroom⟩ := hpre
  let mid := heap + Num.fixedDivideSpace L
  have hmid : mid = heap + Num.fixedDivideSpace L := rfl
  have hspace : L ≤ Num.fixedDivideSpace L := by unfold Num.fixedDivideSpace; omega
  have hmulPtr : mid - L + L = mid := by omega
  have hdivAddr : heap + 9 * L + Num.integerDivideSpace (3 * L) = mid - L := by
    rw [hmid, Num.fixedDivideSpace]
    omega
  have haw := hwords a (by simp)
  have hdw := hwords d (by simp)
  have hLw := hwords L (by simp)
  have hPw := hwords P (by simp)
  have hhw := hwords heap (by simp)
  have hdivFit : Num.Fits h L
      (Num.floorDiv (Num.intVal mem a h L * (2 : ℤ) ^ P) (Num.intVal mem d h L)) := by
    rw [hva.2, hvd.2]
    exact hfit
  apply runs_start_le
  unfold pathNormalizationBody
  refine runs_seq_call_le hd (vs := [a, d, L, P, heap]) (by eval_expr) hwords ?_ ?_
  · exact ⟨⟨a, d, L, P, heap, rfl, hP, ha, hb, hva.1, hvd.1, hvd.2.trans_ne hpos.ne', hdivFit⟩,
      hz, by change mid < 2 ^ w; omega⟩
  · intro ptr mem₁ pos₁ hpost
    obtain ⟨hptr, _, _, hf, hz₁, hvalid, hval⟩ := hpost
    change ptr = mid at hptr
    change (∀ x < heap, mem₁ x = mem x) at hf
    have hptrw : ptr < 2 ^ w := by omega
    have hsubw : mid - L < 2 ^ w := by omega
    have hsub : ptr - L = mid - L := by rw [hptr]
    have hvd₁ := hvd.congr (mem' := mem₁) (fun i hi => hf _ (by omega))
    have hq : PathIntAt mem₁ (mid - L) h L (pathMultiplier P request magnitude) := by
      rw [← hdivAddr]
      refine ⟨hvalid, ?_⟩
      change Num.intVal mem₁ _ h L =
        Num.floorDiv (Num.intVal mem a h L * (2 : ℤ) ^ P) (Num.intVal mem d h L) at hval
      rw [hva.2, hvd.2] at hval
      exact hval
    refine runs_seq_call_le hm (vs := [mid - L, d, L, ptr]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨mid - L, d, L, ptr, rfl, by omega, by omega, hq.1, hvd₁.1⟩,
        hz₁, by change ptr + 6 * L < 2 ^ w; omega⟩
    · intro ret mem₂ pos₂ hp₂
      obtain ⟨hret, _, _, hf₂, hz₂, hpvalid, hpval⟩ := hp₂
      change ret = ptr + 6 * L at hret
      change (∀ x < ptr, mem₂ x = mem₁ x) at hf₂
      change Num.intVal mem₂ (ptr + 4 * L) h (2 * L) =
        Num.intVal mem₁ (mid - L) h L * Num.intVal mem₁ d h L at hpval
      rw [hq.2, hvd₁.2] at hpval
      have hretw : ret < 2 ^ w := by omega
      have hproductAddr : ret - 2 * L = ptr + 4 * L := by omega
      have hproduct : PathIntAt mem₂ (ret - 2 * L) h (2 * L)
          (pathMultiplier P request magnitude * magnitude) := hproductAddr ▸ ⟨hpvalid, hpval⟩
      refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · exact ⟨a, d, L, P, heap, rfl, by change ret = mid + 6 * L; omega,
          hq.congr (fun i hi => hf₂ _ (by omega)), hproduct,
          fun x hx => (hf₂ x (by omega)).trans (hf x hx), hz₂⟩
      · simp only [pathNormalizationContract, Num.fixedDivideContract, Num.multiplyContract,
          heapContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size_reg, Expr.size_bin,
          argsSize_cons, argsSize_nil]
        have hcost : 3 * L * (900 * L + 644) + 900 * L + 700 +
            (2 * L * (38 * (2 * L) + 35) + 120 * L + 99) =
            2852 * L ^ 2 + 3022 * L + 799 := by ring
        omega

/-- The product block holds an allowed actual normalization. Its exact
value uses the same multiplier as the flow tags. -/
theorem pathNormalization_output {w h a d L P heap ret : ℕ} {mem mem' : ℕ → ℕ}
    {request magnitude : ℤ} (hmag : 0 < magnitude)
    (hstep : (2 : ℝ) * ((magnitude : ℝ) / (2 : ℝ) ^ P) ≤ (request : ℝ))
    (hout : (pathNormalizationContract w h request magnitude).post [a, d, L, P, heap] mem ret mem') :
    let k := pathMultiplier P request magnitude
    let req := (request : ℝ) / (2 : ℝ) ^ P
    let inner := (-magnitude : ℤ) / (2 : ℝ) ^ P
    let actual := -(((k : ℝ) / (2 : ℝ) ^ P) * inner)
    ScalarAt mem' (ret - 2 * L) h (2 * L) (2 * P) actual ∧ NormalizationWithin req actual := by
  dsimp only
  obtain ⟨a', d', L', P', heap', hargs, _, _, hproduct, _, _⟩ := hout
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
  constructor
  · refine ⟨hproduct.1, ?_⟩
    rw [Num.fixVal, hproduct.2, pathFlow_actualNormalization_dyadic, mul_neg, neg_neg]
  · let inner : ℝ := ((-magnitude : ℤ) : ℝ) / (2 : ℝ) ^ P
    have hi : inner < 0 := div_neg_of_neg_of_pos (by exact_mod_cast neg_neg_of_pos hmag)
      (pow_pos (zero_lt_two : (0 : ℝ) < 2) _)
    have hs : (2 : ℝ) ^ P ≠ 0 := pow_ne_zero _ two_ne_zero
    have hstep' : 2 * (-inner) ≤ ((request : ℝ) / (2 : ℝ) ^ P) * (2 : ℝ) ^ P := by
      rw [div_mul_cancel₀ _ hs]
      simpa [inner, Int.cast_neg, neg_div] using hstep
    have ht := pathFlow_floor_normalization hi P hstep'
    dsimp only at ht
    rw [pathFlow_floor_normalization_dyadic P request (-magnitude), neg_neg] at ht
    simpa only [inner, Int.cast_neg, pathMultiplier] using ht

end MinCostFlow.MinRatio
