module

public import MinCostFlow.MinRatio.InitSparseCoreThresholdLink
public import MinCostFlow.MinRatio.InitThresholdPathLink

/-!
# Workspace for certified threshold endpoints

Choose and align the precision from the growth and graph dimensions.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain

/-- Materialize the coarse threshold scale from the chain depth in
register 75. The choice leaves room for upward rounding of the growth factor. -/
@[expose] def prepareCertifiedThresholdScale (clog : ℕ) : Stmt :=
  .call 119 clog [.bin .mul (.const 2) (.bin .add (.reg 75) (.const 1))] ;;
  .assign 30 (.bin .shiftLeft (.const 1) (.reg 119))

/-- Init computes the coarse threshold scale with one ceiling logarithm. -/
theorem prepareCertifiedThresholdScale_runs
    {w clog depth : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (h75 : st.regs 75 = depth) (hfit : 2 * (depth + 1) + 1 < 2 ^ w)
    (hscale : concreteThresholdScale depth < 2 ^ w) :
    ∃ out cost, Runs w p ω (prepareCertifiedThresholdScale clog) st .normal out cost ∧
      out.regs 30 = concreteThresholdScale depth ∧
      out.regs 119 = Nat.clog 2 (2 * (depth + 1)) ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 30 → r ≠ 119 → out.regs r = st.regs r) ∧
      cost ≤ 40 * Nat.clog 2 (2 * (depth + 1)) + 31 := by
  let n := 2 * (depth + 1)
  have htwo : 2 < 2 ^ w := by omega
  have hargs : evalArgs w st [.bin .mul (.const 2) (.bin .add (.reg 75) (.const 1))] =
      some [n] := by
    simp [evalArgs, Expr.eval, BinOp.eval, h75, htwo, show 1 < 2 ^ w by omega,
      show depth + 1 < 2 ^ w by omega, show 2 * (depth + 1) < 2 ^ w by omega, n]
  obtain ⟨mid, c, v, hr, ⟨hm, hval⟩, h30, hf, hcost⟩ :=
    runs_call_of_meetsContract (r := 119) (Scaling.Machine.clogTwo_meetsContract hp n)
      hargs (by simp; omega) ⟨rfl, hfit, htwo⟩ ω
  let out := {mid with regs := Function.update mid.regs 30 (concreteThresholdScale depth)}
  have hr' : Runs w p ω (.assign 30 (.bin .shiftLeft (.const 1) (.reg 119)))
      mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, h30.trans hval, Nat.shiftLeft_eq,
        show 1 < 2 ^ w by omega, show 2 ^ Nat.clog 2 n < 2 ^ w from hscale,
        concreteThresholdScale, n], rfl, rfl, rfl⟩
  refine ⟨out, c + 5, runs_seq_iff.mpr (Or.inr ⟨mid, c, 4, hr, hr', rfl⟩),
    by simp [out], by simpa [out, n] using h30.trans hval, hm, ?_, ?_⟩
  · intro r hne h119
    simpa [out, hne] using hf r h119
  · simp [Scaling.Machine.clogTwoContract, argsSize, Expr.size, n] at hcost
    omega

/-- Prepare both endpoint intervals and the coarse scale. The coefficient
routine passes its fresh cursor to the sparse-core logarithm routine. -/
@[expose] def prepareCertifiedThresholdEndpoints (bits load log pack coefficient clog : ℕ) : Stmt :=
  initRebuildCoefficient bits load log pack coefficient ;;
  initSparseCoreLogForThresholds bits load log pack ;;
  prepareCertifiedThresholdScale clog

/-- The endpoint phase runs the three calculations in allocation order. -/
theorem prepareCertifiedThresholdEndpoints_runs
    {w bits load log pack coefficient clog c₁ c₂ c₃ : ℕ}
    {p : Program} {ω : ℕ → Bool} {st mid ready out : State}
    (hr : Runs w p ω (initRebuildCoefficient bits load log pack coefficient) st .normal mid c₁)
    (ht : Runs w p ω (initSparseCoreLogForThresholds bits load log pack) mid .normal ready c₂)
    (hu : Runs w p ω (prepareCertifiedThresholdScale clog) ready .normal out c₃) :
    Runs w p ω (prepareCertifiedThresholdEndpoints bits load log pack coefficient clog)
      st .normal out (c₁ + c₂ + c₃ + 2) :=
  runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂ + c₃ + 1, hr,
    runs_seq_iff.mpr (Or.inr ⟨ready, c₂, c₃, ht, hu, rfl⟩), by omega⟩)

/-- The final scaling step keeps the endpoint registers and their
allocated blocks available to the rebuild table writer. -/
theorem prepareCertifiedThresholdEndpoints_scaled_runs
    {w bits load log pack coefficient clog c₁ c₂ depth : ℕ}
    {p : Program} {ω : ℕ → Bool} {st mid ready : State}
    (hr : Runs w p ω (initRebuildCoefficient bits load log pack coefficient) st .normal mid c₁)
    (ht : Runs w p ω (initSparseCoreLogForThresholds bits load log pack) mid .normal ready c₂)
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (h75 : ready.regs 75 = depth) (hfit : 2 * (depth + 1) + 1 < 2 ^ w)
    (hscale : concreteThresholdScale depth < 2 ^ w) :
    ∃ out cost, Runs w p ω (prepareCertifiedThresholdEndpoints bits load log pack coefficient clog)
        st .normal out cost ∧
      out.regs 30 = concreteThresholdScale depth ∧
      out.regs 119 = Nat.clog 2 (2 * (depth + 1)) ∧ out.mem = ready.mem ∧
      (∀ r, r ≠ 30 → r ≠ 119 → out.regs r = ready.regs r) ∧
      cost ≤ c₁ + c₂ + 40 * Nat.clog 2 (2 * (depth + 1)) + 33 := by
  obtain ⟨out, c₃, hu, h30, h119, hm, hk, hc⟩ :=
    prepareCertifiedThresholdScale_runs (ω := ω) hp h75 hfit hscale
  exact ⟨out, c₁ + c₂ + c₃ + 2, prepareCertifiedThresholdEndpoints_runs hr ht hu,
    h30, h119, hm, hk, by omega⟩

/-- The logarithm and coarse-scale stages retain the coefficient
interval computed at the start of endpoint preparation. -/
theorem prepareCertifiedThresholdEndpoints_preserves_coefficient
    {w bits load log pack clog c₁ c₂ : ℕ}
    {p : Program} {ω : ℕ → Bool} {mid ready out : State}
    (hr : Runs w p ω (initSparseCoreLogForThresholds bits load log pack) mid .normal ready c₁)
    (ht : Runs w p ω (prepareCertifiedThresholdScale clog) ready .normal out c₂) :
    out.regs 49 = mid.regs 49 ∧ out.regs 51 = mid.regs 51 := by
  constructor
  · exact (runs_preserves_register (by rfl) ht).trans (runs_preserves_register (by rfl) hr)
  · exact (runs_preserves_register (by rfl) ht).trans (runs_preserves_register (by rfl) hr)

/-- The coarse-scale call leaves both logarithm endpoints and the
allocation cursor returned by the logarithm routine intact. -/
theorem prepareCertifiedThresholdScale_preserves_log
    {w clog cost : ℕ} {p : Program} {ω : ℕ → Bool} {st out : State}
    (hr : Runs w p ω (prepareCertifiedThresholdScale clog) st .normal out cost) :
    out.regs 26 = st.regs 26 ∧ out.regs 27 = st.regs 27 ∧ out.regs 99 = st.regs 99 :=
  ⟨runs_preserves_register (by rfl) hr, runs_preserves_register (by rfl) hr,
    runs_preserves_register (by rfl) hr⟩

/-- The explicit endpoint bounds returned by the coefficient and
sparse-core logarithm routines suffice for the table's precision check. -/
theorem certifiedThresholdEndpointBudget
    {kl ku ll lu precision factor depth coefficient input : ℕ}
    (hku : ku ≤ (2 * coefficient + 2) * 2 ^ precision)
    (hlu : lu ≤ (input + 3) * 2 ^ precision)
    (hk : ku - kl ≤ 65536 * coefficient + 2)
    (hl : lu - ll ≤ 4096 * (input + 2))
    (hprecision : Nat.clog 2 (2 * (depth + 1) * factor *
      ((65536 * coefficient + 2) * (input + 3) +
        (2 * coefficient + 2) * (4096 * (input + 2)))) ≤ precision) :
    2 * (depth + 1) * factor * ((ku - kl) * lu + ku * (lu - ll)) ≤
      (2 ^ precision) ^ 2 := by
  apply initSparseCoreCoefficientGap_of_endpoint_bounds hku hlu hk hl
  exact (Nat.le_pow_clog (by decide : 1 < 2) _).trans
    (Nat.pow_le_pow_right (by decide) hprecision)

/-- Add the binary ceiling logarithms of the budget factors to obtain
a precision without forming their product in a machine word. -/
theorem certifiedThresholdEndpointPrecision_le
    (depth factor coefficient input : ℕ) :
    Nat.clog 2 (2 * (depth + 1) * factor *
      ((65536 * coefficient + 2) * (input + 3) +
        (2 * coefficient + 2) * (4096 * (input + 2)))) ≤
      Nat.clog 2 (2 * (depth + 1)) + Nat.clog 2 factor +
        Nat.clog 2 ((65536 * coefficient + 2) * (input + 3) +
          (2 * coefficient + 2) * (4096 * (input + 2))) := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add, pow_add]
  exact Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.le_pow_clog (by decide) _) (Nat.le_pow_clog (by decide) _))
    (Nat.le_pow_clog (by decide) _)

/-- Bound the endpoint gap budget by separate binary logarithms of
the coefficient and logarithm input. The fixed extra bits cover both
absolute error constants. -/
theorem certifiedThresholdEndpointPrecision_separate
    (depth factor coefficient input : ℕ) :
    Nat.clog 2 (2 * (depth + 1) * factor *
      ((65536 * coefficient + 2) * (input + 3) +
        (2 * coefficient + 2) * (4096 * (input + 2)))) ≤
      Nat.clog 2 (2 * (depth + 1)) + Nat.clog 2 factor +
        (17 + Nat.clog 2 (coefficient + 1) + Nat.clog 2 (input + 3)) := by
  apply (certifiedThresholdEndpointPrecision_le depth factor coefficient input).trans
  apply Nat.add_le_add_left
  apply Nat.clog_le_of_le_pow
  have ha : 65536 * coefficient + 2 ≤ 65536 * (coefficient + 1) := by omega
  have hb : 4096 * (input + 2) ≤ 4096 * (input + 3) := by omega
  calc
    _ ≤ 65536 * (coefficient + 1) * (input + 3) +
        (2 * coefficient + 2) * (4096 * (input + 3)) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ ha) (Nat.mul_le_mul_left _ hb)
    _ = 73728 * (coefficient + 1) * (input + 3) := by ring
    _ ≤ 2 ^ 17 * 2 ^ Nat.clog 2 (coefficient + 1) * 2 ^ Nat.clog 2 (input + 3) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by decide) (Nat.le_pow_clog (by decide) _))
        (Nat.le_pow_clog (by decide) _)
    _ = _ := by rw [pow_add, pow_add]

/-- Compute the ceiling logarithms of the runtime multiplier and
the sparse-core logarithm input. -/
@[expose] def prepareCertifiedEndpointLogWidths (clog : ℕ) : Stmt :=
  .call 31 clog [.reg 37] ;;
  .call 32 clog [.bin .add (.reg 92) (.const 3)]

/-- The width calculation is read-only and leaves the source words intact. -/
theorem prepareCertifiedEndpointLogWidths_runs
    {w clog factor input : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (h37 : st.regs 37 = factor) (h92 : st.regs 92 = input)
    (hf : factor + 1 < 2 ^ w) (hi : input + 4 < 2 ^ w) :
    ∃ out cost, Runs w p ω (prepareCertifiedEndpointLogWidths clog) st .normal out cost ∧
      out.regs 31 = Nat.clog 2 factor ∧ out.regs 32 = Nat.clog 2 (input + 3) ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 31 → r ≠ 32 → out.regs r = st.regs r) ∧
      cost ≤ 40 * (Nat.clog 2 factor + Nat.clog 2 (input + 3)) + 50 := by
  have hw : 2 < 2 ^ w := by omega
  have hargs : evalArgs w st [.reg 37] = some [factor] := by simp [evalArgs, Expr.eval, h37]
  obtain ⟨mid, c, v, hr, ⟨hm, hval⟩, h31, hk, hc⟩ :=
    runs_call_of_meetsContract (r := 31) (Scaling.Machine.clogTwo_meetsContract hp factor)
      hargs (by simp; omega) ⟨rfl, hf, hw⟩ ω
  have hargs' : evalArgs w mid [.bin .add (.reg 92) (.const 3)] = some [input + 3] := by
    simp [evalArgs, Expr.eval, BinOp.eval, (hk 92 (by decide)).trans h92,
      show 3 < 2 ^ w by omega, show input + 3 < 2 ^ w by omega]
  obtain ⟨out, d, v', ht, ⟨hm', hval'⟩, h32, hk', hd⟩ :=
    runs_call_of_meetsContract (r := 32) (Scaling.Machine.clogTwo_meetsContract hp (input + 3))
      hargs' (by simp; omega) ⟨rfl, by omega, hw⟩ ω
  refine ⟨out, c + d + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, ht, rfl⟩),
    (hk' 31 (by decide)).trans (h31.trans hval), h32.trans hval', hm'.trans hm,
    fun r hr₁ hr₂ => (hk' r hr₂).trans (hk r hr₁), ?_⟩
  simp [Scaling.Machine.clogTwoContract, argsSize, Expr.size] at hc hd
  omega

/-- The sparse-core logarithm input grows at most as the fourth power
of the padded edge count. -/
theorem certifiedThresholdLogInput_le (M : ℕ) :
    SparseCore.coreNMax (M ^ 2) + M ^ 2 + 3 ≤ 65 * (M + 2) ^ 4 := by
  unfold SparseCore.coreNMax SparseCore.coreSplitMax
  have hm₂ : M ^ 2 ≤ (M + 2) ^ 4 := by
    calc
      _ ≤ (M + 2) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right M 2) _
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  have hm₄ : M ^ 4 ≤ (M + 2) ^ 4 := Nat.pow_le_pow_left (Nat.le_add_right M 2) _
  have ho : 1 ≤ (M + 2) ^ 4 := Nat.one_le_pow _ _ (by omega)
  nlinarith only [hm₂, hm₄, ho]

/-- Once the multiplier and depth are bounded by the padded edge
count, the workspace precision is logarithmic in that count. -/
theorem certifiedThresholdPrecision_edge_bound
    {M depth factor coefficient : ℕ} (hd : depth ≤ M) (hf : factor ≤ M) :
    let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
    Nat.clog 2 (2 * (depth + 1)) + Nat.clog 2 factor +
      (17 + Nat.clog 2 (coefficient + 1) + Nat.clog 2 (input + 3)) ≤
        25 + Nat.clog 2 (coefficient + 1) + 6 * Nat.clog 2 (M + 2) := by
  dsimp only
  let r := Nat.clog 2 (M + 2)
  have hM : M + 2 ≤ 2 ^ r := Nat.le_pow_clog (by decide) _
  have hd' : Nat.clog 2 (2 * (depth + 1)) ≤ 1 + r := by
    apply Nat.clog_le_of_le_pow
    rw [pow_add, pow_one]
    omega
  have hf' : Nat.clog 2 factor ≤ r :=
    Nat.clog_le_of_le_pow ((hf.trans (Nat.le_add_right M 2)).trans hM)
  have hi := certifiedThresholdLogInput_le M
  have hi' : Nat.clog 2 (SparseCore.coreNMax (M ^ 2) + M ^ 2 + 3) ≤ 7 + 4 * r := by
    apply Nat.clog_le_of_le_pow
    rw [pow_add, Nat.mul_comm 4 r, pow_mul]
    exact hi.trans (Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left hM _))
  omega

/-- The padded circulation dimensions bound the logarithm input by a
power of the encoded input base with an exponent fixed by the padding. -/
theorem certifiedThresholdLogInput_solver_power_bound (J : Scaling.Circulation)
    (threshold : ℕ) :
    let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
    let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
    SparseCore.coreNMax (M ^ 2) + M ^ 2 + 3 ≤
      B ^ (7 + 4 * max 2 (Nat.clog 2 threshold + 1)) := by
  dsimp only
  let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
  let M := max (IPM.Machine.solverConnectedAugmented J).m threshold
  let d := max 2 (Nat.clog 2 threshold + 1)
  have hB : 2 ≤ B := by dsimp [B]; omega
  have hM : M + 2 ≤ B ^ d := (solverDepthPaddedSize_power_bounds J threshold).1
  calc
    _ ≤ 65 * (M + 2) ^ 4 := certifiedThresholdLogInput_le M
    _ ≤ B ^ 7 * (B ^ d) ^ 4 :=
      Nat.mul_le_mul ((by decide : 65 ≤ 2 ^ 7).trans (Nat.pow_le_pow_left hB _))
        (Nat.pow_le_pow_left hM _)
    _ = _ := by
      change B ^ 7 * (B ^ d) ^ 4 = B ^ (7 + 4 * d)
      rw [← pow_mul, ← pow_add, Nat.mul_comm d 4]

/-- Separate exponent bounds suffice for both word-sized endpoint
calculations, including the coefficient numerator at twice the precision. -/
theorem certifiedThresholdEndpoint_word_bounds
    {w coefficient input precision growth : ℕ}
    (hc : Nat.clog 2 (coefficient + 3) + 2 * precision < w)
    (hi : Nat.clog 2 (input + 3) + precision < w)
    (hg : Nat.clog 2 growth + precision < w) :
    (coefficient + 3) * (2 ^ precision) ^ 2 < 2 ^ w ∧
      (input + 3) * 2 ^ precision < 2 ^ w ∧
      2 ^ precision * growth < 2 ^ w := by
  have word {a n : ℕ} (h : Nat.clog 2 a + n < w) : a * 2 ^ n < 2 ^ w := by
    calc
      _ ≤ 2 ^ Nat.clog 2 a * 2 ^ n :=
        Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) _)
      _ = 2 ^ (Nat.clog 2 a + n) := (pow_add ..).symm
      _ < _ := Nat.pow_lt_pow_right (by decide) h
  refine ⟨?_, word hi, ?_⟩
  · rw [← pow_mul, Nat.mul_comm precision 2]
    exact word hc
  · rw [Nat.mul_comm]
    exact word hg

/-- Separate bounds on the sparsifier parameters give a fixed-power
bound on the multiplier used to form the affine threshold endpoint. -/
theorem certifiedThresholdFactor_power_bound
    {B depth growth buckets degree dd dg db de : ℕ} (hB : 2 ≤ B)
    (hd : depth + 1 ≤ B ^ dd) (hg : growth ≤ B ^ dg)
    (hb : buckets ≤ B ^ db) (he : degree ≤ B ^ de) :
    11 * (depth + 1) * growth * buckets * (2 * degree + 190) ≤
      B ^ (12 + dd + dg + db + de) := by
  have hp : 1 ≤ B ^ de := Nat.one_le_pow _ _ (by omega)
  have hdeg : 2 * degree + 190 ≤ 192 * B ^ de := by omega
  calc
    _ ≤ 11 * B ^ dd * B ^ dg * B ^ db * (192 * B ^ de) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 11 hd) hg) hb) hdeg
    _ = (11 * 192) * B ^ dd * B ^ dg * B ^ db * B ^ de := by ac_rfl
    _ ≤ B ^ 12 * B ^ dd * B ^ dg * B ^ db * B ^ de := by
      have hc : 11 * 192 ≤ B ^ 12 :=
        (by decide : 11 * 192 ≤ 2 ^ 12).trans (Nat.pow_le_pow_left hB _)
      gcongr
    _ = _ := by simp only [pow_add]

/-- The rounded endpoint scale has polynomial size when the depth term,
the growth multiplier, and the log input have polynomial size.
The coefficient and limb width contribute a fixed exponent. -/
theorem certifiedThresholdEndpoint_scale_power_bound
    {B depth factor coefficient input h dd df di : ℕ} (hB : 2 ≤ B)
    (hd : 2 * (depth + 1) ≤ B ^ dd) (hf : factor ≤ B ^ df)
    (hi : input + 3 ≤ B ^ di) :
    let minimum := Nat.clog 2 (2 * (depth + 1)) + Nat.clog 2 factor +
      (17 + Nat.clog 2 (coefficient + 1) + Nat.clog 2 (input + 3))
    let precision := (minimum + (h - 1)) / h * h
    2 ^ precision ≤ B ^ (2 * (dd + df + di) + 17 + Nat.clog 2 (coefficient + 1) + (h - 1)) := by
  dsimp only
  let q := Nat.log 2 B + 1
  have hq : B ≤ 2 ^ q := (Nat.lt_pow_succ_log_self (by decide) B).le
  have hq' : 2 ^ q ≤ B ^ 2 := by
    calc
      _ = 2 ^ Nat.log 2 B * 2 := pow_succ ..
      _ ≤ B * 2 := Nat.mul_le_mul_right _ (Nat.pow_log_le_self _ (by omega))
      _ ≤ B ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_left _ hB
  have clog_le {x e : ℕ} (hx : x ≤ B ^ e) : Nat.clog 2 x ≤ q * e := by
    apply Nat.clog_le_of_le_pow
    rw [pow_mul]
    exact hx.trans (Nat.pow_le_pow_left hq _)
  have hd' := clog_le hd
  have hf' := clog_le hf
  have hi' := clog_le hi
  let offset := 17 + Nat.clog 2 (coefficient + 1) + (h - 1)
  have hp : (Nat.clog 2 (2 * (depth + 1)) + Nat.clog 2 factor +
      (17 + Nat.clog 2 (coefficient + 1) + Nat.clog 2 (input + 3)) + (h - 1)) / h * h
      ≤ q * (dd + df + di) + offset := by
    apply (Nat.div_mul_le_self _ _).trans
    simpa only [offset, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hd' hf') hi')
        (17 + Nat.clog 2 (coefficient + 1) + (h - 1))
  calc
    _ ≤ 2 ^ (q * (dd + df + di) + offset) := Nat.pow_le_pow_right (by decide) hp
    _ = (2 ^ q) ^ (dd + df + di) * 2 ^ offset := by rw [pow_add, pow_mul]
    _ ≤ (B ^ 2) ^ (dd + df + di) * B ^ offset :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hq' _) (Nat.pow_le_pow_left hB _)
    _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; dsimp [offset]; omega

/-- Polynomial bounds on the endpoint inputs and scale give one fixed
word-size multiplier for all three scaled endpoint calculations. -/
theorem certifiedThresholdEndpoint_wordSize_bounds
    (words : List ℕ) {c coefficient input precision growth dc di ds dg : ℕ} :
    let B := words.length + words.foldr max 0 + 2
    coefficient + 3 ≤ B ^ dc → input + 3 ≤ B ^ di →
    2 ^ precision ≤ B ^ ds → growth ≤ B ^ dg →
    max (dc + 2 * ds) (max (di + ds) (ds + dg)) + 1 ≤ c →
    (coefficient + 3) * (2 ^ precision) ^ 2 < 2 ^ wordSize c words ∧
      (input + 3) * 2 ^ precision < 2 ^ wordSize c words ∧
      2 ^ precision * growth < 2 ^ wordSize c words := by
  dsimp only
  intro hc hi hs hg hw
  let B := words.length + words.foldr max 0 + 2
  have hB : 0 < B := by dsimp [B]; omega
  have fit {x e : ℕ} (hx : x ≤ B ^ e) (he : e ≤ c) :
      x < 2 ^ wordSize c words :=
    (hx.trans (Nat.pow_le_pow_right hB he)).trans_lt
      (pow_lt_two_pow_wordSize (by omega) words)
  have hcoef : (coefficient + 3) * (2 ^ precision) ^ 2 ≤ B ^ (dc + 2 * ds) := by
    rw [Nat.mul_comm 2 ds, pow_add, pow_mul]
    exact Nat.mul_le_mul hc (Nat.pow_le_pow_left hs _)
  have hin : (input + 3) * 2 ^ precision ≤ B ^ (di + ds) := by
    rw [pow_add]
    exact Nat.mul_le_mul hi hs
  have hgrowth : 2 ^ precision * growth ≤ B ^ (ds + dg) := by
    rw [pow_add]
    exact Nat.mul_le_mul hs hg
  exact ⟨fit hcoef (by omega), fit hin (by omega), fit hgrowth (by omega)⟩

/-- The workspace already has enough limbs for the affine numerator
after scaling to the coarse table precision. -/
theorem certifiedEndpointWorkspace_affine_bits
    {h M precision coarse : ℕ}
    (hh : 0 < h) (hcoarse : coarse ≤ precision) :
    let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
    let limbs := precision + (input + 2).size + 4
    1 + Nat.clog 2 (M + 1) + 2 * precision + coarse < h * (4 * limbs) := by
  dsimp only
  let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
  have hM : M + 1 ≤ input + 2 := by
    have hs : M ≤ M ^ 2 := Nat.le_self_pow (by decide) _
    dsimp [input]
    omega
  have hr : Nat.clog 2 (M + 1) ≤ (input + 2).size :=
    Nat.clog_le_of_le_pow (hM.trans (Nat.size_le.mp (le_refl (input + 2).size)).le)
  have hb := Nat.le_mul_of_pos_left (4 * (precision + (input + 2).size + 4)) hh
  change 1 + Nat.clog 2 (M + 1) + 2 * precision + coarse < h * (4 * (precision + (input + 2).size + 4))
  omega

/-- The range and guard limbs suffice for the encoded input of each
logarithm. They also cover the upper endpoint of the sparse-core logarithm. -/
theorem certifiedEndpointWorkspace_log_capacity
    {h input precision : ℕ} (hh : 0 < h) :
    let range := (input + 2).size
    let limbs := precision + range + 4
    precision + range + 4 ≤ h * limbs ∧
      4 * 2 ^ precision < Num.capacity h limbs ∧
      2 * ((input + 2) * 2 ^ precision) < Num.capacity h limbs ∧
      2 * ((input + 3) * 2 ^ precision) < Num.capacity h limbs := by
  dsimp only
  let range := (input + 2).size
  let limbs := precision + range + 4
  have hlimbs : limbs ≤ h * limbs := Nat.le_mul_of_pos_left _ hh
  have hinput : input + 3 ≤ 2 ^ range := by
    exact Nat.size_le.mp (le_refl (input + 2).size)
  have hbig : 2 * ((input + 3) * 2 ^ precision) < Num.capacity h limbs := by
    calc
      _ ≤ 2 * (2 ^ range * 2 ^ precision) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hinput)
      _ = 2 ^ (1 + range + precision) := by simp [pow_add, Nat.mul_assoc]
      _ < _ := by
        rw [Num.capacity, Num.base, ← pow_mul]
        exact Nat.pow_lt_pow_right (by decide) (by have he : limbs = precision + range + 4 := rfl; omega)
  have hm (n : ℕ) (hn : n ≤ input + 3) :
      2 * (n * 2 ^ precision) < Num.capacity h limbs :=
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hn)).trans_lt hbig
  exact ⟨hlimbs, (by simpa only [← Nat.mul_assoc] using hm 2 (by omega)), hm (input + 2) (by omega), hbig⟩

/-- Add the separate precision bounds after their ceiling logarithms
have been computed. The coefficient logarithm depends on the fixed witness. -/
@[expose] def stageCertifiedEndpointPrecision (coefficient : ℕ) : Stmt :=
  .assign 37 (.bin .add (.bin .add (.reg 119) (.reg 31))
    (.bin .add (.const (17 + Nat.clog 2 (coefficient + 1))) (.reg 32)))

/-- The word sum gives a sufficient precision for the endpoint budget. -/
theorem stageCertifiedEndpointPrecision_runs
    {w depth factor coefficient input : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h119 : st.regs 119 = Nat.clog 2 (2 * (depth + 1)))
    (h31 : st.regs 31 = Nat.clog 2 factor)
    (h32 : st.regs 32 = Nat.clog 2 (input + 3))
    (hword : Nat.clog 2 (2 * (depth + 1)) + Nat.clog 2 factor +
      (17 + Nat.clog 2 (coefficient + 1) + Nat.clog 2 (input + 3)) < 2 ^ w) :
    ∃ out, Runs w p ω (stageCertifiedEndpointPrecision coefficient) st .normal out 8 ∧
      out.regs 37 = Nat.clog 2 (2 * (depth + 1)) + Nat.clog 2 factor +
        (17 + Nat.clog 2 (coefficient + 1) + Nat.clog 2 (input + 3)) ∧
      out.mem = st.mem ∧ (∀ r ≠ 37, out.regs r = st.regs r) := by
  let a := Nat.clog 2 (2 * (depth + 1)) + Nat.clog 2 factor
  let b := 17 + Nat.clog 2 (coefficient + 1) + Nat.clog 2 (input + 3)
  let out := {st with regs := Function.update st.regs 37 (a + b)}
  have ha : a < 2 ^ w := by dsimp [a]; omega
  have hb : b < 2 ^ w := by dsimp [b]; omega
  have hc : 17 + Nat.clog 2 (coefficient + 1) < 2 ^ w := by dsimp [b] at hb; omega
  dsimp [a] at ha
  dsimp [b] at hb
  exact ⟨out, runs_assign_iff.mpr ⟨_, by
    simp [Expr.eval, BinOp.eval, h119, h31, h32, hc, a, b, ha, hb, hword],
    rfl, rfl, rfl⟩, by simp [out, a, b], rfl, fun r hr => by simp [out, hr]⟩

/-- Compute the minimum precision for the weighted endpoint gap. -/
@[expose] def prepareCertifiedEndpointPrecision (clog coefficient : ℕ) : Stmt :=
  prepareCertifiedEndpointLogWidths clog ;; stageCertifiedEndpointPrecision coefficient

/-- The chosen minimum precision bounds the full integer budget. -/
theorem prepareCertifiedEndpointPrecision_runs
    {w clog depth factor coefficient input : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (h37 : st.regs 37 = factor) (h92 : st.regs 92 = input)
    (h119 : st.regs 119 = Nat.clog 2 (2 * (depth + 1)))
    (hf : factor + 1 < 2 ^ w) (hi : input + 4 < 2 ^ w)
    (hword : Nat.clog 2 (2 * (depth + 1)) + Nat.clog 2 factor +
      (17 + Nat.clog 2 (coefficient + 1) + Nat.clog 2 (input + 3)) < 2 ^ w) :
    ∃ out cost, Runs w p ω (prepareCertifiedEndpointPrecision clog coefficient) st .normal out cost ∧
      out.regs 37 = Nat.clog 2 (2 * (depth + 1)) + Nat.clog 2 factor +
        (17 + Nat.clog 2 (coefficient + 1) + Nat.clog 2 (input + 3)) ∧
      Nat.clog 2 (2 * (depth + 1) * factor *
        ((65536 * coefficient + 2) * (input + 3) +
          (2 * coefficient + 2) * (4096 * (input + 2)))) ≤ out.regs 37 ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 31 → r ≠ 32 → r ≠ 37 → out.regs r = st.regs r) ∧
      cost ≤ 40 * (Nat.clog 2 factor + Nat.clog 2 (input + 3)) + 59 := by
  obtain ⟨mid, c, hr, h31, h32, hm, hk, hc⟩ :=
    prepareCertifiedEndpointLogWidths_runs (ω := ω) hp h37 h92 hf hi
  obtain ⟨out, ht, hprec, hm', hk'⟩ :=
    stageCertifiedEndpointPrecision_runs (p := p) (ω := ω)
      ((hk 119 (by decide) (by decide)).trans h119) h31 h32 hword
  exact ⟨out, c + 9, runs_seq_iff.mpr (Or.inr ⟨mid, c, 8, hr, ht, by omega⟩),
    hprec, (certifiedThresholdEndpointPrecision_separate depth factor coefficient input).trans
      hprec.symm.le, hm'.trans hm, fun r h31r h32r h37r => (hk' r h37r).trans (hk r h31r h32r),
    by omega⟩

/-- Align the endpoint precision and allocate the corresponding
numeric format in the workspace registers. -/
@[expose] def prepareCertifiedEndpointWorkspace (clog coefficient h : ℕ) : Stmt :=
  prepareCertifiedEndpointPrecision clog coefficient ;; stageRebuildLogWorkspace h

/-- Limb alignment preserves the precision bound obtained from the
coefficient and logarithm endpoint errors. -/
theorem prepareCertifiedEndpointWorkspace_runs
    {w clog depth factor coefficient input h range : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (h37 : st.regs 37 = factor) (h92 : st.regs 92 = input)
    (h119 : st.regs 119 = Nat.clog 2 (2 * (depth + 1))) (h127 : st.regs 127 = range)
    (hf : factor + 1 < 2 ^ w) (hi : input + 4 < 2 ^ w)
    (hh : 0 < h) (hhw : h < 2 ^ w) :
    let bits := Nat.clog 2 (2 * (depth + 1)) + Nat.clog 2 factor +
      (17 + Nat.clog 2 (coefficient + 1) + Nat.clog 2 (input + 3))
    let precision := (bits + (h - 1)) / h * h
    bits + (h - 1) < 2 ^ w → precision + range + 4 < 2 ^ w → 2 ^ precision < 2 ^ w →
    ∃ out cost, Runs w p ω (prepareCertifiedEndpointWorkspace clog coefficient h) st .normal out cost ∧
      out.regs 68 = precision ∧ out.regs 67 = precision + range + 4 ∧ out.regs 4 = 2 ^ precision ∧
      Nat.clog 2 (2 * (depth + 1) * factor *
        ((65536 * coefficient + 2) * (input + 3) +
          (2 * coefficient + 2) * (4096 * (input + 2)))) ≤ precision ∧
      Nat.clog 2 (2 * (depth + 1)) ≤ precision ∧ 16 ≤ precision ∧
      (input + 2).size + 11 ≤ precision ∧
      precision < bits + h ∧ h ∣ precision ∧ out.mem = st.mem ∧
      cost ≤ 40 * (Nat.clog 2 factor + Nat.clog 2 (input + 3)) + 80 := by
  dsimp only
  intro htop hlimbs hscale
  obtain ⟨mid, c, hr, hbits, hbound, hm, hk, hc⟩ :=
    prepareCertifiedEndpointPrecision_runs (ω := ω) (coefficient := coefficient) hp h37 h92 h119 hf hi (by omega)
  obtain ⟨out, ht, h68, h67, h4, hlo, hhi, hdvd, hm', _⟩ :=
    stageRebuildLogWorkspace_runs (p := p) (ω := ω) hh hhw hbits
      ((hk 127 (by decide) (by decide) (by decide)).trans h127) htop hlimbs hscale
  have hrange : (input + 2).size ≤ Nat.clog 2 (input + 3) := by
    apply Nat.size_le.mpr
    exact (show input + 2 < input + 3 by omega).trans_le (Nat.le_pow_clog (by decide) _)
  have hguard : (input + 2).size + 11 ≤
      ((Nat.clog 2 (2 * (depth + 1)) + Nat.clog 2 factor +
        (17 + Nat.clog 2 (coefficient + 1) + Nat.clog 2 (input + 3)) + (h - 1)) / h) * h :=
    (show (input + 2).size + 11 ≤ _ by omega).trans hlo
  exact ⟨out, c + 21, runs_seq_iff.mpr (Or.inr ⟨mid, c, 20, hr, ht, by omega⟩),
    h68, h67, h4, hbound.trans (hbits.symm ▸ hlo),
    (Nat.le_add_right _ _ |>.trans (Nat.le_add_right _ _) |>.trans hlo), by omega, hguard, hhi, hdvd, hm'.trans hm, by omega⟩

/-- Stage the logarithm argument from the range routine's cached word. -/
@[expose] def stageCertifiedEndpointLogInput : Stmt :=
  .assign 92 (.bin .sub (.reg 124) (.const 2))

/-- The cached word includes the offset used by the logarithm routine. -/
theorem stageCertifiedEndpointLogInput_runs
    {w input : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h124 : st.regs 124 = input + 2) (hw : input + 2 < 2 ^ w) :
    ∃ out, Runs w p ω stageCertifiedEndpointLogInput st .normal out 4 ∧
      out.regs 92 = input ∧ out.mem = st.mem ∧
      (∀ r ≠ 92, out.regs r = st.regs r) := by
  let out := {st with regs := Function.update st.regs 92 input}
  have htwo : 2 < 2 ^ w := by omega
  have hi : input < 2 ^ w := by omega
  exact ⟨out, runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, h124, htwo, hi],
    rfl, rfl, rfl⟩, by simp [out], rfl, fun r hr => by simp [out, hr]⟩

/-- Select and install the endpoint workspace, then restore the graph
vertex count for the two logarithm routines. -/
@[expose] def installCertifiedEndpointWorkspace (clog coefficient h : ℕ) : Stmt :=
  stageCertifiedEndpointLogInput ;;
  prepareCertifiedEndpointWorkspace clog coefficient h ;;
  .assign 92 (.reg 57)

/-- The saved vertex count survives workspace selection. -/
theorem installCertifiedEndpointWorkspace_runs
    {w clog coefficient h input c N : ℕ}
    {p : Program} {ω : ℕ → Bool} {st ready : State}
    (h124 : st.regs 124 = input + 2) (hw : input + 2 < 2 ^ w)
    (h57 : st.regs 57 = N)
    (hr : Runs w p ω (prepareCertifiedEndpointWorkspace clog coefficient h)
      {st with regs := Function.update st.regs 92 input} .normal ready c) :
    ∃ out, Runs w p ω (installCertifiedEndpointWorkspace clog coefficient h)
        st .normal out (c + 8) ∧
      out.regs 92 = N ∧ out.mem = ready.mem ∧
      (∀ r ≠ 92, out.regs r = ready.regs r) := by
  let mid := {st with regs := Function.update st.regs 92 input}
  have hstage : Runs w p ω stageCertifiedEndpointLogInput st .normal mid 4 := by
    apply runs_assign_iff.mpr
    exact ⟨_, by simp [Expr.eval, BinOp.eval, h124, show 2 < 2 ^ w by omega,
      show input < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hkeep := runs_preserves_register (r := 57) (by rfl) hr
  have hv : ready.regs 57 = N := hkeep.trans (by simp [h57])
  let out := {ready with regs := Function.update ready.regs 92 N}
  have ht : Runs w p ω (.assign 92 (.reg 57)) ready .normal out 2 :=
    runs_assign_iff.mpr ⟨_, congrArg some hv, rfl, rfl, rfl⟩
  refine ⟨out, ?_, by simp [out], rfl, fun r hn => by simp [out, hn]⟩
  exact runs_seq_iff.mpr (Or.inr ⟨mid, 4, c + 3, hstage,
    runs_seq_iff.mpr (Or.inr ⟨ready, c, 2, hr, ht, rfl⟩), by omega⟩)

/-- Workspace installation returns the aligned precision bounds and the
original vertex count together. -/
theorem installCertifiedEndpointWorkspace_certified_runs
    {w clog depth factor coefficient input h range vertices : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (h37 : st.regs 37 = factor) (h124 : st.regs 124 = input + 2)
    (h57 : st.regs 57 = vertices)
    (h119 : st.regs 119 = Nat.clog 2 (2 * (depth + 1))) (h127 : st.regs 127 = range)
    (hf : factor + 1 < 2 ^ w) (hi : input + 4 < 2 ^ w)
    (hh : 0 < h) (hhw : h < 2 ^ w) :
    let bits := Nat.clog 2 (2 * (depth + 1)) + Nat.clog 2 factor +
      (17 + Nat.clog 2 (coefficient + 1) + Nat.clog 2 (input + 3))
    let precision := (bits + (h - 1)) / h * h
    bits + (h - 1) < 2 ^ w → precision + range + 4 < 2 ^ w → 2 ^ precision < 2 ^ w →
    ∃ out cost, Runs w p ω (installCertifiedEndpointWorkspace clog coefficient h) st .normal out cost ∧
      out.regs 68 = precision ∧ out.regs 67 = precision + range + 4 ∧ out.regs 4 = 2 ^ precision ∧
      Nat.clog 2 (2 * (depth + 1) * factor *
        ((65536 * coefficient + 2) * (input + 3) +
          (2 * coefficient + 2) * (4096 * (input + 2)))) ≤ precision ∧
      Nat.clog 2 (2 * (depth + 1)) ≤ precision ∧ 16 ≤ precision ∧
      (input + 2).size + 11 ≤ precision ∧
      out.regs 92 = vertices ∧ precision < bits + h ∧ h ∣ precision ∧ out.mem = st.mem ∧
      cost ≤ 40 * (Nat.clog 2 factor + Nat.clog 2 (input + 3)) + 88 := by
  dsimp only
  intro htop hlimbs hscale
  let mid := {st with regs := Function.update st.regs 92 input}
  obtain ⟨ready, c, hr, h68, h67, h4, hBudget, hCoarseBits, hCoefficientBits, hGuard, hhi, hdvd, hm, hc⟩ :=
    prepareCertifiedEndpointWorkspace_runs (ω := ω) (st := mid) hp
      (by simp [mid, h37]) (by simp [mid]) (by simp [mid, h119]) (by simp [mid, h127])
      hf hi hh hhw htop hlimbs hscale
  obtain ⟨out, ht, h92, hm', hk⟩ :=
    installCertifiedEndpointWorkspace_runs h124 (by omega) h57 hr
  exact ⟨out, c + 8, ht, (hk 68 (by decide)).trans h68, (hk 67 (by decide)).trans h67,
    (hk 4 (by decide)).trans h4, hBudget, hCoarseBits, hCoefficientBits, hGuard, h92, hhi, hdvd, hm'.trans hm, by omega⟩

/-- Compute the input range and then install the threshold endpoint workspace. -/
@[expose] def rangeAndInstallCertifiedEndpointWorkspace (bits clog coefficient h : ℕ) : Stmt :=
  stageRebuildLogRange bits ;; installCertifiedEndpointWorkspace clog coefficient h

/-- The runtime range supplies both the workspace width and the
logarithm guard-bit bound. -/
theorem rangeAndInstallCertifiedEndpointWorkspace_runs
    {w bits clog depth factor coefficient M h vertices : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hb : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hM : st.regs 22 = M) (hN : st.regs 92 = vertices) (hpos : 0 < M)
    (h37 : st.regs 37 = factor) (h119 : st.regs 119 = Nat.clog 2 (2 * (depth + 1)))
    (hf : factor + 1 < 2 ^ w) (hh : 0 < h) (hhw : h < 2 ^ w) :
    let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
    let range := (input + 2).size
    let minimum := Nat.clog 2 (2 * (depth + 1)) + Nat.clog 2 factor +
      (17 + Nat.clog 2 (coefficient + 1) + Nat.clog 2 (input + 3))
    let precision := (minimum + (h - 1)) / h * h
    input + 4 < 2 ^ w → minimum + (h - 1) < 2 ^ w →
    precision + range + 4 < 2 ^ w → 2 ^ precision < 2 ^ w →
    ∃ out cost, Runs w p ω (rangeAndInstallCertifiedEndpointWorkspace bits clog coefficient h)
        st .normal out cost ∧
      out.regs 68 = precision ∧ out.regs 67 = precision + range + 4 ∧ out.regs 4 = 2 ^ precision ∧
      Nat.clog 2 (2 * (depth + 1) * factor *
        ((65536 * coefficient + 2) * (input + 3) +
          (2 * coefficient + 2) * (4096 * (input + 2)))) ≤ precision ∧
      Nat.clog 2 (2 * (depth + 1)) ≤ precision ∧ 16 ≤ precision ∧
      range + 11 ≤ precision ∧ out.regs 92 = vertices ∧ h ∣ precision ∧ out.mem = st.mem ∧
      cost ≤ 14 * range + 40 * (Nat.clog 2 factor + Nat.clog 2 (input + 3)) + 125 := by
  dsimp only
  intro hi htop hlimbs hscale
  obtain ⟨mid, c, hr, h127, h124, _, h57, hm, hk, hc⟩ :=
    stageRebuildLogRange_runs (ω := ω) hb hM hN hpos (by omega)
  obtain ⟨out, d, ht, h68, h67, h4, hBudget, hCoarseBits, hCoefficientBits, hGuard, h92, _, hdvd, hm', hd⟩ :=
    installCertifiedEndpointWorkspace_certified_runs (ω := ω) hp
      ((hk 37 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h37) h124 h57
      ((hk 119 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h119)
      h127 hf hi hh hhw htop hlimbs hscale
  exact ⟨out, c + d + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, ht, rfl⟩),
    h68, h67, h4, hBudget, hCoarseBits, hCoefficientBits, hGuard, h92, hdvd, hm'.trans hm, by omega⟩

/-- Derive the endpoint workspace from the sparse-core dimensions and
the exact length factor before computing either logarithm enclosure. -/
@[expose] def initCertifiedEndpointWorkspace (power bits clog coefficient h : ℕ) : Stmt :=
  prepareCertifiedThresholdScale clog ;;
  initSparseCoreGrowthWords power ;;
  rangeAndInstallCertifiedEndpointWorkspace bits clog coefficient h

/-- The workspace allocation uses the computed growth multiplier and
the cached input range in sequence. -/
theorem initCertifiedEndpointWorkspace_runs
    {w power bits clog coefficient h c₁ c₂ c₃ : ℕ}
    {p : Program} {ω : ℕ → Bool} {st scaled growth out : State}
    (hr : Runs w p ω (prepareCertifiedThresholdScale clog) st .normal scaled c₁)
    (ht : Runs w p ω (initSparseCoreGrowthWords power) scaled .normal growth c₂)
    (hu : Runs w p ω (rangeAndInstallCertifiedEndpointWorkspace bits clog coefficient h)
      growth .normal out c₃) :
    Runs w p ω (initCertifiedEndpointWorkspace power bits clog coefficient h)
      st .normal out (c₁ + c₂ + c₃ + 2) :=
  runs_seq_iff.mpr (Or.inr ⟨scaled, c₁, c₂ + c₃ + 1, hr,
    runs_seq_iff.mpr (Or.inr ⟨growth, c₂, c₃, ht, hu, rfl⟩), by omega⟩)

/-- Runtime growth and graph dimensions determine the installed workspace. -/
theorem initCertifiedEndpointWorkspace_sized_runs
    {w power bits clog depth sparseDepth growth growthScale buckets degree coefficient M h vertices : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hb : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hM : st.regs 22 = M) (hN : st.regs 92 = vertices) (hpos : 0 < M)
    (hpow : MeetsContract w p power (initStretchPowerContract w))
    (h75 : st.regs 75 = depth) (hDepth : 2 * (depth + 1) + 1 < 2 ^ w)
    (hcoarse : concreteThresholdScale depth < 2 ^ w)
    (h44 : st.regs 44 = sparseDepth) (h50 : st.regs 50 = growthScale * growth)
    (h4 : st.regs 4 = growthScale) (hs : 0 < growthScale) (hg : 0 < growth)
    (hSparseDepth : max (sparseDepth + 1) 3 < 2 ^ w)
    (hScaled : growthScale * growth < 2 ^ w)
    (hFirst : 3 ^ sparseDepth * growth ^ (sparseDepth + 1) < 2 ^ w)
    (h47 : st.regs 47 = buckets) (h48 : st.regs 48 = degree) (hbPos : 0 < buckets)
    (hh : 0 < h) (hhw : h < 2 ^ w) (hw : 11 < 2 ^ w) :
    let factor := 11 * (sparseDepth + 1) * growth * buckets * (2 * degree + 190)
    let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
    let range := (input + 2).size
    let minimum := Nat.clog 2 (2 * (depth + 1)) + Nat.clog 2 factor +
      (17 + Nat.clog 2 (coefficient + 1) + Nat.clog 2 (input + 3))
    let precision := (minimum + (h - 1)) / h * h
    factor + 1 < 2 ^ w → input + 4 < 2 ^ w → minimum + (h - 1) < 2 ^ w →
    precision + range + 4 < 2 ^ w → 2 ^ precision < 2 ^ w →
    ∃ out cost, Runs w p ω (initCertifiedEndpointWorkspace power bits clog coefficient h)
        st .normal out cost ∧
      out.regs 68 = precision ∧ out.regs 67 = precision + range + 4 ∧ out.regs 4 = 2 ^ precision ∧
      Nat.clog 2 (2 * (depth + 1) * factor *
        ((65536 * coefficient + 2) * (input + 3) +
          (2 * coefficient + 2) * (4096 * (input + 2)))) ≤ precision ∧
      Nat.clog 2 (2 * (depth + 1)) ≤ precision ∧ 16 ≤ precision ∧
      range + 11 ≤ precision ∧ out.regs 35 = growth ∧ out.regs 92 = vertices ∧ h ∣ precision ∧ out.mem = st.mem ∧
      cost ≤ 14 * range + 40 * (Nat.clog 2 factor + Nat.clog 2 (input + 3) +
        Nat.clog 2 (2 * (depth + 1))) + 40 * sparseDepth + 237 := by
  dsimp only
  intro hf hi htop hlimbs hscale
  obtain ⟨scaled, c₁, hr, _, h119, hm, hk, hc⟩ :=
    prepareCertifiedThresholdScale_runs (ω := ω) hp h75 hDepth hcoarse
  have keep₁ (r : ℕ) (h₁ : r ≠ 30 := by decide) (h₂ : r ≠ 119 := by decide) := hk r h₁ h₂
  have hFactor : 11 * ((sparseDepth + 1) * buckets * (2 * degree + 190)) * growth < 2 ^ w := by
    apply lt_of_le_of_lt _ hf
    rw [show 11 * ((sparseDepth + 1) * buckets * (2 * degree + 190)) * growth =
      11 * (sparseDepth + 1) * growth * buckets * (2 * degree + 190) by ac_rfl]
    omega
  obtain ⟨growthState, c₂, ht, h35, _, h37, hm', hk', hc'⟩ :=
    initSparseCoreGrowthWords_runs (ω := ω) hpow ((keep₁ 44).trans h44)
      ((keep₁ 50).trans h50) ((keep₁ 4).trans h4) hs hg hSparseDepth hScaled
      hFirst ((keep₁ 47).trans h47) ((keep₁ 48).trans h48) hbPos hw hFactor
  have keep₂ (r : ℕ) (hr : r ∉ ([33, 34, 35, 36, 37, 38, 45] : List ℕ) := by decide) :=
    hk' r hr
  obtain ⟨out, c₃, hu, h68, h67, h4', hBudget, hCoarseBits, hCoefficientBits, hGuard, h92, hdvd, hm'', hc''⟩ :=
    rangeAndInstallCertifiedEndpointWorkspace_runs (ω := ω) hp hb
      ((keep₂ 22).trans ((keep₁ 22).trans hM)) ((keep₂ 92).trans ((keep₁ 92).trans hN)) hpos
      h37 ((keep₂ 119).trans h119) hf hh hhw hi htop hlimbs hscale
  exact ⟨out, c₁ + c₂ + c₃ + 2, initCertifiedEndpointWorkspace_runs hr ht hu,
    h68, h67, h4', hBudget, hCoarseBits, hCoefficientBits, hGuard,
    (runs_preserves_register (by rfl) hu).trans h35, h92, hdvd, hm''.trans (hm'.trans hm), by omega⟩

end MinCostFlow.MinRatio
