module

public import MinCostFlow.MinRatio.DetectorThreshold
public import MinCostFlow.MinRatio.PathPayloadLayout
public import MinCostFlow.Num.FixedDivide

/-!
# Computing the initial detection residual

The proof of Theorem 5.1 (pages 29–30) starts each edge at minus the
detection threshold. With integer numerators this is the floor quotient
of the negated threshold parameter and the positive edge length. The
shared fixed-point divider computes that quotient exactly.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Arguments are the negated epsilon block, length block, limb count,
precision, and heap. The result occupies the last block of the allocation. -/
noncomputable def detectorResidualContract (w h : ℕ) (epsilon : ℤ) (length : ℕ) : Contract where
  pre args mem := ∃ a d L P heap, args = [a, d, L, P, heap] ∧ h ∣ P ∧
    a + L ≤ heap ∧ d + L ≤ heap ∧ 0 < length ∧
    PathIntAt mem a h L (-epsilon) ∧ PathIntAt mem d h L length ∧
    Num.Fits h L (-detectorThreshold P ((epsilon : ℝ) / (2 : ℝ) ^ P)
      ((length : ℝ) / (2 : ℝ) ^ P)) ∧
    ZeroFrom mem heap ∧ heap + Num.fixedDivideSpace L < 2 ^ w
  post args mem ret mem' := ∃ a d L P heap, args = [a, d, L, P, heap] ∧
    ret = heap + Num.fixedDivideSpace L ∧
    PathIntAt mem' (ret - L) h L
      (-detectorThreshold P ((epsilon : ℝ) / (2 : ℝ) ^ P) ((length : ℝ) / (2 : ℝ) ^ P)) ∧
    (∀ x < heap, mem' x = mem x) ∧ ZeroFrom mem' ret
  cost args _ := 2700 * (args.getD 2 0) ^ 2 + 2832 * args.getD 2 0 + 700

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM

private theorem divisor_floor_eq_residual (P : ℕ) (epsilon : ℤ) {length : ℕ} (hl : 0 < length) :
    Num.floorDiv ((-epsilon) * (2 : ℤ) ^ P) length =
      -detectorThreshold P ((epsilon : ℝ) / (2 : ℝ) ^ P) ((length : ℝ) / (2 : ℝ) ^ P) := by
  have hlen : ¬ (length : ℤ) < 0 := Int.not_lt.mpr (Int.natCast_nonneg _)
  rw [detectorThreshold_dyadic P epsilon length hl, neg_neg, Num.floorDiv, ite_eq_right hlen, neg_mul]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

/-- The divider's negative threshold result fits when the encoded
epsilon and length satisfy the detector's magnitude bounds. -/
theorem detectorResidual_pre_of_bounds {w h L P E a d heap : ℕ} {mem : ℕ → ℕ}
    (epsilon : ℤ) (length : ℕ) (hP : h ∣ P)
    (ha : a + L ≤ heap) (hd : d + L ≤ heap)
    (he : PathIntAt mem a h L (-epsilon)) (hl : PathIntAt mem d h L length)
    (heps : 0 < (epsilon : ℝ) / (2 : ℝ)^P)
    (hepsU : (epsilon : ℝ) / (2 : ℝ)^P ≤ (2 : ℝ)^E)
    (hlen : 1 / (2 : ℝ)^E ≤ (length : ℝ) / (2 : ℝ)^P)
    (hw : P + 2 * E + 3 ≤ h * L) (hz : ZeroFrom mem heap)
    (hroom : heap + Num.fixedDivideSpace L < 2 ^ w) :
    (detectorResidualContract w h epsilon length).pre [a, d, L, P, heap] mem := by
  have hpos : 0 < length := by
    have hq : 0 < (length : ℝ) / (2 : ℝ)^P :=
      (one_div_pos.mpr (pow_pos zero_lt_two _)).trans_le hlen
    have hl' := (lt_div_iff₀ (pow_pos (zero_lt_two : (0 : ℝ) < 2) P)).mp hq
    rw [zero_mul] at hl'
    exact_mod_cast hl'
  exact ⟨a, d, L, P, heap, rfl, hP, ha, hd, hpos, he, hl,
    detectorThreshold_reset_fits _ _ heps hepsU hlen hw, hz, hroom⟩

/-- The shared divider writes the exact negative threshold residue.
Its quadratic cost depends on the limb count alone. -/
theorem detectorResidual_meetsContract {w h entry : ℕ} {p : Program} (epsilon : ℤ)
    (length : ℕ) (hdivide : MeetsContract w p entry (Num.fixedDivideContract w h)) :
    MeetsContract w p entry (detectorResidualContract w h epsilon length) := by
  intro args mem pos ω hwords hpre
  obtain ⟨a, d, L, P, heap, rfl, hP, ha, hd, hl, hea, hld, hfit, hz, hroom⟩ := hpre
  have hpos : (0 : ℤ) < length := Int.natCast_pos.mpr hl
  have hval := divisor_floor_eq_residual P epsilon hl
  have hquot : Num.floorDiv (Num.intVal mem a h L * (2 : ℤ) ^ P) (Num.intVal mem d h L) =
      -detectorThreshold P ((epsilon : ℝ) / (2 : ℝ) ^ P) ((length : ℝ) / (2 : ℝ) ^ P) := by
    rw [hea.2, hld.2, hval]
  rw [← hquot] at hfit
  have hdivPre : (Num.fixedDivideContract w h).pre [a, d, L, P, heap] mem :=
    ⟨⟨a, d, L, P, heap, rfl, hP, ha, hd, hea.1, hld.1, hld.2.trans_ne hpos.ne', hfit⟩, hz, hroom⟩
  obtain ⟨body, hb, out, st, c, hrun, hpost, hc⟩ := hdivide _ _ _ _ hwords hdivPre
  obtain ⟨hret, _, _, hf, hz', hvalid, hout⟩ := hpost
  change out.value = heap + Num.fixedDivideSpace L at hret
  have haddr : out.value - L = heap + 9 * L + Num.integerDivideSpace (3 * L) := by
    rw [hret, Num.fixedDivideSpace]
    omega
  refine ⟨body, hb, out, st, c, hrun, ⟨a, d, L, P, heap, rfl, hret, ?_, hf, hz'⟩, ?_⟩
  · rw [haddr]
    exact ⟨hvalid, hout.trans hquot⟩
  · refine hc.trans ?_
    change (3 * L) * (900 * L + 644) + 900 * L + 700 ≤ 2700 * L ^ 2 + 2832 * L + 700
    exact le_of_eq (by ring)

end MinCostFlow.MinRatio
