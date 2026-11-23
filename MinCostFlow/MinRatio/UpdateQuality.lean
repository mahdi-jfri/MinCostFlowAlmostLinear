module

public import MinCostFlow.Num.IPM.AlphaFacts
public import MinCostFlow.Chain.Algorithm2
public import MinCostFlow.MinRatio.ShiftGuards
public import MinCostFlow.MinRatio.PathPayloadLayout
public import MinCostFlow.Num.ShiftRight
public import MinCostFlow.Num.Less
public import MinCostFlow.Num.Subtract
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# The Update quality comparison

Algorithm 2 (page 29) compares the cycle ratio to the negative quality
threshold. With the solver's dyadic parameters, the comparison uses
signed integers, including when the cycle has zero weighted length.
-/

public section

namespace MinCostFlow.MinRatio

/-- For equal fixed-point scales, the quality test of Algorithm 2
(page 29) is an integer sign and magnitude comparison. A zero denominator
fails because division by zero in the model gives zero. -/
theorem updateQuality_dyadic_iff (m U k precision : ℕ) (inner norm : ℤ) (hn : 0 ≤ norm) :
    (inner / (2 : ℝ) ^ precision) / (norm / (2 : ℝ) ^ precision) ≤
        -((1 / (2 : ℝ) ^ k) * (Num.IPM.alphaPrime m U / 8)) ↔
      0 < norm ∧ inner * (2 : ℤ) ^ (k + Num.IPM.alphaExponent m U + 3) ≤ -norm := by
  let q := k + Num.IPM.alphaExponent m U + 3
  have hq : 0 < (2 : ℝ) ^ q := by positivity
  have hscale : (2 : ℝ) ^ precision ≠ 0 := by positivity
  have hthreshold :
      (1 / (2 : ℝ) ^ k) * (Num.IPM.alphaPrime m U / 8) = 1 / (2 : ℝ) ^ q := by
    simp only [q, Num.IPM.alphaPrime, pow_add]
    norm_num
    ring
  rw [hthreshold, div_div_div_cancel_right₀ hscale]
  by_cases hz : norm = 0
  · subst norm
    simp
  · have hnz : 0 < norm := lt_of_le_of_ne hn (Ne.symm hz)
    have hnReal : 0 < (norm : ℝ) := by exact_mod_cast hnz
    rw [and_iff_right hnz, div_le_iff₀ hnReal]
    have heq : -(1 / (2 : ℝ) ^ q) * (norm : ℝ) = -(norm : ℝ) / (2 : ℝ) ^ q := by ring
    rw [heq, le_div_iff₀ hq]
    exact_mod_cast (Iff.rfl :
      inner * (2 : ℤ) ^ q ≤ -norm ↔ inner * (2 : ℤ) ^ q ≤ -norm)

/-- Shift the negative weighted length right to avoid growing the
numerator. The signed floor quotient gives the exact comparison even
when the weighted length is not a multiple of the threshold scale. -/
theorem updateQuality_floor_iff (m U k precision : ℕ) (inner norm : ℤ) (hn : 0 ≤ norm) :
    (inner / (2 : ℝ) ^ precision) / (norm / (2 : ℝ) ^ precision) ≤
        -((1 / (2 : ℝ) ^ k) * (Num.IPM.alphaPrime m U / 8)) ↔
      0 < norm ∧ inner ≤ -norm / (2 : ℤ) ^ (k + Num.IPM.alphaExponent m U + 3) := by
  rw [updateQuality_dyadic_iff m U k precision inner norm hn,
    Int.le_ediv_iff_mul_le (by positivity)]

open WordRAM

/-- Compare the numerator against the shifted negative weighted length.
Register 0 points to the negative length, register 1 to the numerator,
and registers 2 through 4 hold the limb count, shift, and heap. -/
@[expose] def updateQualityCompareBody (shift less : ℕ) : Stmt :=
  .call 5 shift [.reg 0, .reg 2, .reg 3, .reg 4] ;;
  .call 6 less [.bin .add (.bin .add (.reg 4) (.reg 2)) (.const 1), .reg 1, .reg 2] ;;
  .ret (.bin .sub (.const 1) (.reg 6))

/-- The positive-length comparison uses two scratch blocks and returns
one when the cycle passes the dyadic acceptance test of Algorithm 2. -/
@[expose] noncomputable def updateQualityCompareContract
    (w h m U k precision : ℕ) (inner norm : ℤ) : Contract where
  pre args mem := ∃ d a L heap,
    args = [d, a, L, k + Num.IPM.alphaExponent m U + 3, heap] ∧
    1 < 2 ^ w ∧ 0 < norm ∧ d + L ≤ heap ∧ a + L ≤ heap ∧
    PathIntAt mem d h L (-norm) ∧ PathIntAt mem a h L inner ∧
    ZeroFrom mem heap ∧ heap + 2 * L + 1 < 2 ^ w
  post args mem ret mem' :=
    ret = (if (inner / (2 : ℝ) ^ precision) / (norm / (2 : ℝ) ^ precision) ≤
      -((1 / (2 : ℝ) ^ k) * (Num.IPM.alphaPrime m U / 8)) then 1 else 0) ∧
    (∀ x < heapArg args, mem' x = mem x) ∧
    ZeroFrom mem' (heapArg args + 2 * args.getD 2 0 + 1)
  cost args _ := 107 * args.getD 2 0 + 180

/-- The arithmetic right shift and signed comparison implement the
positive-length quality test in linear time in the limb count. -/
theorem updateQualityCompare_meetsContract
    {w h m U k precision entry shift less : ℕ} {p : Program} (inner norm : ℤ)
    (hp : p.HasAt entry [updateQualityCompareBody shift less])
    (hs : MeetsContract w p shift (Num.shiftRightContract w h))
    (hl : MeetsContract w p less (Num.lessContract w h)) :
    MeetsContract w p entry (updateQualityCompareContract w h m U k precision inner norm) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨d, a, L, heap, rfl, hw, hnorm, hd, ha, hD, hA, hz, hroom⟩ := hpre
  let q := k + Num.IPM.alphaExponent m U + 3
  have hqw : q < 2 ^ w := hwords q (by simp [q])
  have hdw : d < 2 ^ w := hwords d (by simp)
  have haw : a < 2 ^ w := hwords a (by simp)
  have hLw : L < 2 ^ w := hwords L (by simp)
  have hhw : heap < 2 ^ w := hwords heap (by simp)
  apply runs_start_le
  unfold updateQualityCompareBody
  refine runs_seq_call_le hs (vs := [d, L, q, heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨d, L, q, heap, rfl, hd, hD.1⟩, hz, by simpa [heapArg, Nat.add_assoc] using hroom⟩
  · intro top mem' pos' hpost
    obtain ⟨htop, _, _, hframe, hzero, hvalid, hval⟩ := hpost
    change top = heap + (2 * L + 1) at htop
    change Num.Valid mem' (heap + L + 1) h L at hvalid
    change Num.intVal mem' (heap + L + 1) h L =
      Num.intVal mem d h L / (2 : ℤ) ^ q at hval
    rw [hD.2] at hval
    have hA' := hA.congr (mem' := mem') fun j hj => hframe _ (by
      change a + j < heap
      omega)
    have hfirst : heap + L < 2 ^ w := by omega
    have hsecond : heap + L + 1 < 2 ^ w := by omega
    refine runs_seq_call_le hl (vs := [heap + L + 1, a, L]) (by eval_expr)
      (by wram_words) ?_ ?_
    · exact ⟨_, a, L, rfl, by omega, by omega, hvalid, hA'.1⟩
    · intro bit mem'' pos'' hcmp
      obtain ⟨hm, hbit⟩ := hcmp
      change mem'' = mem' at hm
      subst mem''
      change bit = (if Num.intVal mem' (heap + L + 1) h L < Num.intVal mem' a h L then 1 else 0) at hbit
      rw [hval, hA'.2] at hbit
      have hf := updateQuality_floor_iff m U k precision inner norm hnorm.le
      have hqiff : _ ↔ inner ≤ -norm / (2 : ℤ) ^ q := hf.trans (and_iff_right hnorm)
      have hb : bit ≤ 1 := by rw [hbit]; split <;> omega
      have hwb : bit < 2 ^ w := by omega
      have hout : 1 - bit < 2 ^ w := by omega
      refine runs_ret_le (v := 1 - bit) (by eval_expr) ?_ ?_
      · refine ⟨?_, hframe, ?_⟩
        · rw [hbit]
          by_cases hgood : inner ≤ -norm / (2 : ℤ) ^ q
          · rw [ite_eq_right (not_lt_of_ge hgood), ite_eq_left (hqiff.mpr hgood)]
            rfl
          · rw [ite_eq_left (lt_of_not_ge hgood), ite_eq_right (fun h => hgood (hqiff.mp h))]
            rfl
        · rw [htop] at hzero
          simpa [heapArg, Nat.add_assoc] using hzero
      · simp [Expr.size, argsSize, Num.shiftRightContract, Num.lessContract, heapContract, updateQualityCompareContract]
        omega

/-- Check for zero weighted length before calling the positive-length
comparison. Both procedures take the same fixed-point input blocks. -/
@[expose] def updateQualityBody (sign compare : ℕ) : Stmt :=
  .call 5 sign [.reg 0, .reg 2] ;;
  .cond (.reg 5)
    (.call 6 compare [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4] ;; .ret (.reg 6))
    (.ret (.const 0))

/-- The acceptance test takes a nonnegative weighted length and its
negative fixed-point encoding, with the same outputs as the positive test. -/
@[expose] noncomputable def updateQualityContract
    (w h m U k precision : ℕ) (inner norm : ℤ) : Contract :=
  let C := updateQualityCompareContract w h m U k precision inner norm
  { C with
    pre := fun args mem => ∃ d a L heap,
      args = [d, a, L, k + Num.IPM.alphaExponent m U + 3, heap] ∧
      1 < 2 ^ w ∧ 0 ≤ norm ∧ d + L ≤ heap ∧ a + L ≤ heap ∧
      PathIntAt mem d h L (-norm) ∧ PathIntAt mem a h L inner ∧
      ZeroFrom mem heap ∧ heap + 2 * L + 1 < 2 ^ w
    cost := fun args _ => 107 * args.getD 2 0 + 210 }

/-- The zero and positive cases implement the exact dyadic Update test.
A zero weighted length returns zero and leaves the heap untouched. -/
theorem updateQuality_meetsContract
    {w h m U k precision entry sign compare : ℕ} {p : Program} (inner norm : ℤ)
    (hp : p.HasAt entry [updateQualityBody sign compare])
    (hs : MeetsContract w p sign (Num.isNegativeContract w h))
    (hc : MeetsContract w p compare (updateQualityCompareContract w h m U k precision inner norm)) :
    MeetsContract w p entry (updateQualityContract w h m U k precision inner norm) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨d, a, L, heap, rfl, hw, hn, hd, ha, hD, hA, hz, hroom⟩ := hpre
  let q := k + Num.IPM.alphaExponent m U + 3
  have hdw := hwords d (by simp)
  have haw := hwords a (by simp)
  have hLw := hwords L (by simp)
  have hqw : q < 2 ^ w := hwords q (by simp [q])
  have hhw := hwords heap (by simp)
  apply runs_start_le
  unfold updateQualityBody
  refine runs_seq_call_le hs (vs := [d, L]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨d, L, rfl, by omega, hD.1⟩
  · intro bit mem' pos' hsign
    obtain ⟨hm, hb⟩ := hsign
    change mem' = mem at hm
    subst mem'
    change bit = (if Num.intVal mem d h L < 0 then 1 else 0) at hb
    rw [hD.2] at hb
    have hbWord : bit < 2 ^ w := by rw [hb]; split <;> omega
    refine runs_cond_le (v := bit) (by eval_expr) ?_ ?_
    · intro hnonzero
      have hpos : 0 < norm := by
        by_contra h
        exact hnonzero (hb.trans (ite_eq_right (by omega)))
      refine runs_seq_call_le hc (vs := [d, a, L, q, heap]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨d, a, L, heap, rfl, hw, hpos, hd, ha, hD, hA, hz, hroom⟩
      · intro ret mem' pos' hcpost
        have hretWord : ret < 2 ^ w := by
          have hret := hcpost.1
          rw [hret]
          split <;> omega
        refine runs_ret_le (v := ret) (by eval_expr) hcpost ?_
        simp [Expr.size, argsSize, updateQualityContract, updateQualityCompareContract, Num.isNegativeContract]
        omega
    · intro hnone
      have hnorm : norm = 0 := by
        by_contra hne
        have hneg : -norm < 0 := by omega
        rw [ite_eq_left hneg] at hb
        omega
      have hfail : ¬ (inner / (2 : ℝ) ^ precision) / (norm / (2 : ℝ) ^ precision) ≤
          -((1 / (2 : ℝ) ^ k) * (Num.IPM.alphaPrime m U / 8)) :=
        fun h => (by omega : ¬ 0 < norm) ((updateQuality_floor_iff m U k precision inner norm hn).mp h).1
      refine runs_ret_le (v := 0) (by eval_expr) ?_ ?_
      · exact ⟨(ite_eq_right hfail).symm, fun _ _ => rfl, fun x hx => hz x (by
          change heap + 2 * L + 1 ≤ x at hx
          omega)⟩
      · simp [Expr.size, argsSize, updateQualityContract, Num.isNegativeContract]

/-- Use the first free block as a zero operand to negate the weighted
length, then run the dyadic acceptance test. -/
@[expose] def updateQualityFromNormBody (subtract quality : ℕ) : Stmt :=
  .call 5 subtract [.reg 4, .reg 0, .reg 2, .bin .add (.reg 4) (.reg 2)] ;;
  .call 6 quality [.bin .add (.reg 4) (.bin .add (.reg 2) (.reg 2)),
    .reg 1, .reg 2, .reg 3, .reg 5] ;;
  .ret (.reg 6)

/-- The two input blocks contain the weighted length and numerator at the
same fixed-point scale. Scratch extends through five limb blocks and a word. -/
@[expose] noncomputable def updateQualityFromNormContract
    (w h m U k precision : ℕ) (inner norm : ℤ) : Contract :=
  let C := updateQualityContract w h m U k precision inner norm
  { C with
    pre := fun args mem => ∃ d a L heap,
      args = [d, a, L, k + Num.IPM.alphaExponent m U + 3, heap] ∧
      1 < 2 ^ w ∧ 0 ≤ norm ∧ d + L ≤ heap ∧ a + L ≤ heap ∧
      PathIntAt mem d h L norm ∧ PathIntAt mem a h L inner ∧
      ZeroFrom mem heap ∧ heap + 5 * L + 1 < 2 ^ w
    post := fun args mem ret mem' =>
      ret = (if (inner / (2 : ℝ) ^ precision) / (norm / (2 : ℝ) ^ precision) ≤
        -((1 / (2 : ℝ) ^ k) * (Num.IPM.alphaPrime m U / 8)) then 1 else 0) ∧
      (∀ x < heapArg args, mem' x = mem x) ∧
      ZeroFrom mem' (heapArg args + 5 * args.getD 2 0 + 1)
    cost := fun args _ => 181 * args.getD 2 0 + 285 }

/-- Compute the exact dyadic acceptance bit from the stored numerator
and nonnegative weighted length in linear time in the limb count. -/
theorem updateQualityFromNorm_meetsContract
    {w h m U k precision entry subtract quality : ℕ} {p : Program} (inner norm : ℤ)
    (hp : p.HasAt entry [updateQualityFromNormBody subtract quality])
    (hs : MeetsContract w p subtract (Num.subtractContract w h))
    (hq : MeetsContract w p quality (updateQualityContract w h m U k precision inner norm)) :
    MeetsContract w p entry (updateQualityFromNormContract w h m U k precision inner norm) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨d, a, L, heap, rfl, hw, hn, hd, ha, hD, hA, hz, hroom⟩ := hpre
  let q := k + Num.IPM.alphaExponent m U + 3
  have hdw := hwords d (by simp)
  have haw := hwords a (by simp)
  have hLw := hwords L (by simp)
  have hqw : q < 2 ^ w := hwords q (by simp [q])
  have hhw := hwords heap (by simp)
  have hzeroEnd : heap + L < 2 ^ w := by omega
  have hzero : PathIntAt mem heap h L 0 :=
    ⟨Num.zeroFrom_valid hz le_rfl, Num.intVal_zeroFrom hz le_rfl⟩
  have hfit := Num.intVal_fits hD.1
  rw [hD.2] at hfit
  have hnegFit : Num.Fits h L (-norm) := by
    rcases hfit with ⟨hl, hu⟩
    have hc := Num.capacity_pos h L
    exact ⟨by omega, by omega⟩
  apply runs_start_le
  unfold updateQualityFromNormBody
  refine runs_seq_call_le hs (vs := [heap, d, L, heap + L]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨_, d, L, _, rfl, le_rfl, by omega, hzero.1, hD.1⟩,
      fun x hx => hz x (by change heap + L ≤ x at hx; omega),
      by change heap + L + 2 * L < 2 ^ w; omega⟩
  · intro top mem' pos' hpost
    obtain ⟨htop, _, _, hframe, htail, hvalid, hval⟩ := hpost
    change top = heap + L + 2 * L at htop
    change (∀ x < heap + L, mem' x = mem x) at hframe
    change Num.Valid mem' (heap + L + L) h L at hvalid
    change Num.intVal mem' (heap + L + L) h L =
      Num.wrap h L (Num.intVal mem heap h L - Num.intVal mem d h L) at hval
    rw [hzero.2, hD.2, zero_sub, Num.wrap_of_fits hnegFit] at hval
    have hneg : PathIntAt mem' (heap + (L + L)) h L (-norm) := by
      simpa only [Nat.add_assoc] using (show PathIntAt mem' (heap + L + L) h L (-norm) from ⟨hvalid, hval⟩)
    have hinner := hA.congr (mem' := mem') (fun j hj => hframe _ (by omega))
    have h2L : L + L < 2 ^ w := by omega
    have hnegw : heap + (L + L) < 2 ^ w := by omega
    have htopw : top < 2 ^ w := by omega
    refine runs_seq_call_le hq (vs := [heap + (L + L), a, L, q, top])
      (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨_, a, L, top, rfl, hw, hn, by omega, by omega, hneg, hinner, htail, by omega⟩
    · intro bit mem'' pos'' hout
      obtain ⟨hb, hf, hz'⟩ := hout
      have hbitw : bit < 2 ^ w := by rw [hb]; split <;> omega
      refine runs_ret_le (v := bit) (by eval_expr) ?_ ?_
      · exact ⟨hb, fun x hx => (hf x (by change x < top; change x < heap at hx; omega)).trans
          (hframe x (by change x < heap at hx; omega)), fun x hx => hz' x (by
            change top + 2 * L + 1 ≤ x
            change heap + 5 * L + 1 ≤ x at hx
            omega)⟩
      · simp [Expr.size, argsSize, Num.subtractContract, heapContract,
          updateQualityContract, updateQualityFromNormContract]
        omega

/-- The stored acceptance bit is the guard used by `algorithm2_loopWith`
for the solver's dyadic quality exponent. The caller supplies the cycle
inner product and weighted norm at the comparison precision. -/
theorem updateQualityFromNorm_bit_eq_loopGuard
    {w h m U k precision innerAddr normAddr limbs heap bit : ℕ}
    {cfg : Chain.Alg2Config} {G : MGraph} {g len cycle : ℕ → ℝ}
    {inner norm : ℤ} {mem mem' : ℕ → ℕ}
    (hα : cfg.α = Num.IPM.alphaPrime m U / 8)
    (hinner : G.inner g cycle = inner / (2 : ℝ) ^ precision)
    (hnorm : G.lnorm len cycle = norm / (2 : ℝ) ^ precision)
    (hpost : (updateQualityFromNormContract w h m U k precision inner norm).post
      [normAddr, innerAddr, limbs, k + Num.IPM.alphaExponent m U + 3, heap] mem bit mem') :
    bit = (if G.inner g cycle / G.lnorm len cycle ≤ -((1 / (2 : ℝ) ^ k) * cfg.α)
      then 1 else 0) := by
  rw [hα, hinner, hnorm]
  exact hpost.1

/-- Algorithm 2 (page 29) runs the two shift failure checks only after
the quality test rejects the cycle. Register 61 holds the quality bit. -/
@[expose] def updateQualityDispatch : Stmt :=
  .cond (.reg 61) .nop checkAndRecordShift

/-- Accepting a cycle skips both checks and leaves the state unchanged. -/
theorem updateQualityDispatch_accept_runs
    {w : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hbit : st.regs 61 = 1) :
    Runs w p ω updateQualityDispatch st .normal st 3 := by
  exact runs_cond_iff.mpr ⟨1, 1, by simp [Expr.eval, hbit], by
    exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩

/-- On rejection, the dispatch performs the supplied verified run of the
two failure checks and increments the shift counter only if both pass. -/
theorem updateQualityDispatch_reject_runs
    {w cost : ℕ} {p : Program} {st out : State} {ω : ℕ → Bool}
    (hbit : st.regs 61 = 0)
    (hchecks : Runs w p ω checkAndRecordShift st .normal out cost) :
    Runs w p ω updateQualityDispatch st .normal out (cost + 2) := by
  exact runs_cond_iff.mpr ⟨0, cost, by simp [Expr.eval, hbit], hchecks, by simp [Expr.size]; omega⟩

/-- Call the quality comparison without reusing the shift check's argument
registers. Registers 62 through 66 hold its two pointers, width, exponent,
and scratch start. -/
@[expose] def callUpdateQuality (entry : ℕ) : Stmt :=
  .call 61 entry [.reg 62, .reg 63, .reg 64, .reg 65, .reg 66]

/-- The linked quality call sets just the quality register and frames
memory below its scratch heap, ready for the failure checks. -/
theorem callUpdateQuality_runs
    {w h m U k precision entry d a limbs heap : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool} (inner norm : ℤ)
    (hc : MeetsContract w p entry (updateQualityFromNormContract w h m U k precision inner norm))
    (hd : st.regs 62 = d) (ha : st.regs 63 = a) (hL : st.regs 64 = limbs)
    (hq : st.regs 65 = k + Num.IPM.alphaExponent m U + 3) (hh : st.regs 66 = heap)
    (hwords : ∀ x ∈ [d, a, limbs, k + Num.IPM.alphaExponent m U + 3, heap], x < 2 ^ w)
    (hpre : (updateQualityFromNormContract w h m U k precision inner norm).pre
      [d, a, limbs, k + Num.IPM.alphaExponent m U + 3, heap] st.mem) :
    ∃ out cost, Runs w p ω (callUpdateQuality entry) st .normal out cost ∧
      cost ≤ 181 * limbs + 291 ∧
      (∀ r, r ≠ 61 → out.regs r = st.regs r) ∧
      (updateQualityFromNormContract w h m U k precision inner norm).post
        [d, a, limbs, k + Num.IPM.alphaExponent m U + 3, heap]
        st.mem (out.regs 61) out.mem := by
  obtain ⟨body, hbody, o, result, c, hrun, hpost, hcost⟩ :=
    hc _ st.mem st.pos ω hwords hpre
  let out := { result with regs := Function.update st.regs 61 o.value }
  have hcall : Runs w p ω (callUpdateQuality entry) st .normal out (5 + c + 1) :=
    runs_call_iff.mpr ⟨_, body, o, result, c,
      by simp [evalArgs, Expr.eval, hd, ha, hL, hq, hh], hbody, hrun, rfl, rfl, rfl⟩
  have hc' : c ≤ 181 * limbs + 285 := hcost
  refine ⟨out, 5 + c + 1, hcall, by omega, ?_, ?_⟩
  · intro r hr
    simp [out, Function.update_of_ne hr]
  · simpa only [out, Function.update_self] using hpost

/-- The quality call and both failure checks at the start of an
Algorithm 2 loop iteration (page 29). -/
@[expose] def updateQualityAndChecks (entry : ℕ) : Stmt :=
  callUpdateQuality entry ;; updateQualityDispatch

/-- The quality call preserves the tables below its scratch heap. If the
cycle fails the quality test, the two checks return the model's eligible
shift, or failure, and record the increment for a permitted shift. -/
theorem updateQualityAndChecks_runs
    {cfg : Chain.Alg2Config} (model : Chain.Alg2State cfg)
    {w h m U k precision entry d a limbs heap passBase countBase quotaBase : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool} (inner norm : ℤ)
    (hc : MeetsContract w p entry (updateQualityFromNormContract w h m U k precision inner norm))
    (hd : st.regs 62 = d) (ha : st.regs 63 = a) (hL : st.regs 64 = limbs)
    (hq : st.regs 65 = k + Num.IPM.alphaExponent m U + 3) (hh : st.regs 66 = heap)
    (hwords : ∀ x ∈ [d, a, limbs, k + Num.IPM.alphaExponent m U + 3, heap], x < 2 ^ w)
    (hpre : (updateQualityFromNormContract w h m U k precision inner norm).pre
      [d, a, limbs, k + Num.IPM.alphaExponent m U + 3, heap] st.mem)
    (hTables : shiftCheckTablesAt st.mem passBase countBase quotaBase model)
    (hpBase : st.regs 0 = passBase)
    (hpasses : st.regs 1 = ⌈2 * Chain.alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊)
    (hdepth : st.regs 21 = cfg.P.d + 1)
    (hcBase : st.regs 3 = countBase) (hqBase : st.regs 4 = quotaBase)
    (hpEnd : passBase + cfg.P.d < heap) (hcEnd : countBase + cfg.P.d < heap)
    (hqEnd : quotaBase + cfg.P.d < heap) (hdepthWord : cfg.P.d + 1 < 2 ^ w)
    (hw : 1 < 2 ^ w) (hquotaWords : ∀ i ≤ cfg.P.d, st.mem (quotaBase + i) < 2 ^ w) :
    let psi := Chain.alg2PsiGame cfg.Ψ cfg.P.M₀
    let accepted := (Chain.findEligibleLevel cfg.P.d psi model.passes).bind fun i =>
      if (model.chain.shiftCount i.val : ℝ) + 1 ≤
          Chain.gameShiftBound cfg.P psi model.chain.rebuildCount i.val then some i.val else none
    let good := (inner / (2 : ℝ) ^ precision) / (norm / (2 : ℝ) ^ precision) ≤
      -((1 / (2 : ℝ) ^ k) * (Num.IPM.alphaPrime m U / 8))
    ∃ out cost, Runs w p ω (updateQualityAndChecks entry) st .normal out cost ∧
      cost ≤ 181 * limbs + 20 * (cfg.P.d + 1) + 347 ∧
      (if good then
        out.regs 61 = 1 ∧ (∀ addr < heap, out.mem addr = st.mem addr)
      else
        out.regs 2 = (if accepted.isSome then 1 else 0) ∧
        (∀ i ∈ accepted, out.regs 5 = i) ∧
        ∀ addr < heap, out.mem addr = accepted.elim st.mem
          (fun i => Function.update st.mem (countBase + i) (model.chain.shiftCount i + 1)) addr) := by
  dsimp only
  obtain ⟨mid, c, hr, hcost, hregs, hbit, hframe, _⟩ :=
    callUpdateQuality_runs inner norm hc hd ha hL hq hh hwords hpre
  have hheap := hwords heap (by simp)
  change ∀ addr < heap, mid.mem addr = st.mem addr at hframe
  by_cases hgood : (inner / (2 : ℝ) ^ precision) / (norm / (2 : ℝ) ^ precision) ≤
      -((1 / (2 : ℝ) ^ k) * (Num.IPM.alphaPrime m U / 8))
  · rw [ite_eq_left hgood] at hbit
    refine ⟨mid, c + 4, runs_seq_iff.mpr (Or.inr ⟨mid, c, 3, hr,
      updateQualityDispatch_accept_runs hbit, by omega⟩), by omega, ?_⟩
    rw [ite_eq_left hgood]
    exact ⟨hbit, hframe⟩
  · rw [ite_eq_right hgood] at hbit
    have ht : shiftCheckTablesAt mid.mem passBase countBase quotaBase model := by
      refine ⟨fun i => ?_, fun i hi => ?_, fun i hi => ?_⟩
      · have := i.isLt
        exact (hframe _ (by omega)).trans (hTables.1 i)
      · exact (hframe _ (by omega)).trans (hTables.2.1 i hi)
      · exact (hframe _ (by omega)).trans (hTables.2.2 i hi)
    obtain ⟨out, time, hrun, htime, _, hout, hchosen, hmem⟩ :=
      checkAndRecordShift_runs (ω := ω) model ht
        ((hregs 0 (by decide)).trans hpBase) ((hregs 1 (by decide)).trans hpasses)
        ((hregs 21 (by decide)).trans hdepth) ((hregs 3 (by decide)).trans hcBase)
        ((hregs 4 (by decide)).trans hqBase)
        (hpEnd.trans hheap) (hcEnd.trans hheap) (hqEnd.trans hheap) hdepthWord hw
        (fun i hi => (hframe _ (by omega)).trans_lt (hquotaWords i hi))
    refine ⟨out, c + time + 3, runs_seq_iff.mpr (Or.inr ⟨mid, c, time + 2, hr,
      updateQualityDispatch_reject_runs hbit hrun, by omega⟩), by omega, ?_⟩
    rw [ite_eq_right hgood]
    refine ⟨hout, hchosen, fun addr haddr => ?_⟩
    rw [hmem]
    let chosen := (Chain.findEligibleLevel cfg.P.d (Chain.alg2PsiGame cfg.Ψ cfg.P.M₀) model.passes).bind
      fun i => if (model.chain.shiftCount i.val : ℝ) + 1 ≤
        Chain.gameShiftBound cfg.P (Chain.alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val
        then some i.val else none
    change chosen.elim mid.mem _ addr = chosen.elim st.mem _ addr
    cases chosen with
    | none => exact hframe addr haddr
    | some i => by_cases he : addr = countBase + i <;> simp [Option.elim, he, hframe addr haddr]

end MinCostFlow.MinRatio
