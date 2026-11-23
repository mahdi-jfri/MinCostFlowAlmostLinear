module

public import MinCostFlow.IPM.Machine.MinRatioContract
public import WordRAM.CopyWords
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Failure-branch output writer for `Update`

When `Update` fails (`result.2 = none`), `minRatioMachineContractWithV` operation 0
still requires writing:
- `AnswerAt mem' heap none` (`mem' heap = 0`), and
- `ScalarAt mem' (heap + 1) 4 (2 * L) (2 * P) actual` with
  `NormalizationWithin requested actual`.

Since `requested = Num.fixVal mem eta 4 L P > 0`, `4 ∣ P`, and `P ≤ 4 * L`, shifting the
`L` limbs of `eta` up by `P / 4` limbs inside the zero-initialized `2 * L`-limb block
`[heap + 1, heap + 1 + 2 * L)` produces the exact scalar `actual = requested` in
`O(L)` steps, satisfying `NormalizationWithin requested requested` trivially.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine

/-- Fixed deterministic failure-output procedure taking `[eta, L, P, heap]`.
Writes `0` at `heap`, shifts the positive `L`-limb scalar at `eta` left by `P / 4` limbs
into `[heap + 1, heap + 1 + 2 * L)`, and returns `heap + 1 + 2 * L`. -/
@[expose] def updateFailOutputBody (copyWords : ℕ) : Stmt :=
  .store (.reg 3) (.const 0) ;;
  .assign 4 (.bin .add (.bin .add (.reg 3) (.const 1)) (.bin .div (.reg 2) (.const 4))) ;;
  .call 5 copyWords [.reg 0, .reg 4, .reg 1] ;;
  .ret (.bin .add (.bin .add (.reg 3) (.const 1)) (.bin .mul (.const 2) (.reg 1)))

theorem updateFailOutputBody_noRand (copyWords : ℕ) :
    (updateFailOutputBody copyWords).NoRand := by
  simp [updateFailOutputBody, Stmt.NoRand]

/-- Helper: `unsignedVal` of `k` leading zeros followed by `n` limbs equals
`(Num.base h) ^ k * unsignedVal` of the shifted block. -/
private theorem unsignedVal_zero_prefix {mem : ℕ → ℕ} {a h : ℕ} :
    ∀ k n, (∀ i < k, mem (a + i) = 0) →
      Num.unsignedVal mem a h (k + n) = Num.base h ^ k * Num.unsignedVal mem (a + k) h n
  | 0, n, _ => by simp
  | k + 1, n, hz => by
    have h0 : mem a = 0 := by simpa using hz 0 (Nat.zero_lt_succ k)
    have htail : ∀ i < k, mem (a + 1 + i) = 0 := fun i hi => by
      have := hz (i + 1) (by omega)
      rwa [show a + (i + 1) = a + 1 + i by omega] at this
    rw [show k + 1 + n = (k + n) + 1 by omega]
    simp only [Num.unsignedVal, h0, zero_add]
    rw [unsignedVal_zero_prefix k n htail, show a + 1 + k = a + (k + 1) by omega,
      pow_succ', mul_assoc]

/-- Helper: `unsignedVal` of `n` limbs followed by `r` trailing zeros equals `unsignedVal`
of the `n`-limb prefix. -/
private theorem unsignedVal_zero_suffix {mem : ℕ → ℕ} {a h : ℕ} :
    ∀ n r, (∀ i < r, mem (a + n + i) = 0) →
      Num.unsignedVal mem a h (n + r) = Num.unsignedVal mem a h n
  | 0, r, hz => by
    induction r generalizing a with
    | zero => rfl
    | succ r ih =>
      have h0 : mem a = 0 := by simpa using hz 0 (Nat.zero_lt_succ r)
      have htail : ∀ i < r, mem (a + 1 + 0 + i) = 0 := fun i hi => by
        have := hz (i + 1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm 1] using this
      simp only [zero_add, Num.unsignedVal, h0]
      have hrec := ih (a := a + 1) htail
      simp only [zero_add, Num.unsignedVal] at hrec
      rw [show Nat.add 0 r = r from Nat.zero_add r, hrec, Nat.mul_zero]
  | n + 1, r, hz => by
    have htail : ∀ i < r, mem (a + 1 + n + i) = 0 := fun i hi => by
      have := hz i hi
      rwa [show a + (n + 1) + i = a + 1 + n + i by omega] at this
    rw [show n + 1 + r = (n + r) + 1 by omega]
    simp only [Num.unsignedVal]
    rw [unsignedVal_zero_suffix n r htail]

/-- Helper: `unsignedVal` agrees when two memories agree on `[a, a + L)`. -/
private theorem unsignedVal_congr {m₁ m₂ : ℕ → ℕ} {a₁ a₂ h : ℕ} :
    ∀ L, (∀ i < L, m₁ (a₁ + i) = m₂ (a₂ + i)) →
      Num.unsignedVal m₁ a₁ h L = Num.unsignedVal m₂ a₂ h L
  | 0, _ => rfl
  | L + 1, hag => by
    simp only [Num.unsignedVal]
    rw [show m₁ a₁ = m₂ a₂ by simpa using hag 0 (Nat.zero_lt_succ L)]
    congr 2
    exact unsignedVal_congr L (fun i hi => by
      have := hag (i + 1) (by omega)
      rwa [show a₁ + (i + 1) = a₁ + 1 + i by omega,
        show a₂ + (i + 1) = a₂ + 1 + i by omega] at this)

/-- `NormalizationWithin x x` holds for any nonnegative `x`. -/
theorem normalizationWithin_self {x : ℝ} (hx : 0 ≤ x) : NormalizationWithin x x :=
  ⟨by linarith, by linarith⟩

/-- Running `updateFailOutputBody` writes `AnswerAt out.mem heap none` and
`ScalarAt out.mem (heap + 1) 4 (2 * L) (2 * P) (Num.fixVal mem eta 4 L P)` in at most
`17 * L + 35` steps, returning `heap + 1 + 2 * L`. -/
theorem updateFailOutputBody_runs {w copyWords eta L P heap pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    (hCopy : MeetsContract w p copyWords (copyWordsContract w))
    (hdiv4 : 4 ∣ P) (hPL : P ≤ 4 * L)
    (hetaDisj : eta + L ≤ heap ∨ heap + 1 + 2 * L ≤ eta) (hetaWEnd : eta + L < 2 ^ w)
    (hvalid : Num.Valid mem eta 4 L)
    (hpos : 0 < Num.fixVal mem eta 4 L P)
    (hz : ∀ j < 2 * L, mem (heap + 1 + j) = 0)
    (hroom : heap + 1 + 2 * L < 2 ^ w) (hw4 : 4 < 2 ^ w) :
    let requested := Num.fixVal mem eta 4 L P
    ∃ cost out,
      Runs w p ω (updateFailOutputBody copyWords)
        (startState [eta, L, P, heap] mem pos) (.returned (heap + 1 + 2 * L)) out cost ∧
      cost ≤ 17 * L + 40 ∧
      AnswerAt out.mem heap none ∧
      ScalarAt out.mem (heap + 1) 4 (2 * L) (2 * P) requested ∧
      NormalizationWithin requested requested ∧
      (∀ a, a < heap ∨ heap + 1 + 2 * L ≤ a → out.mem a = mem a) := by
  dsimp only
  let q := P / 4
  have hPeq : 4 * q = P := Nat.mul_div_cancel' hdiv4
  have hqLeL : q ≤ L := by omega
  have hLW : L < 2 ^ w := by omega
  have hetaW : eta < 2 ^ w := by omega
  have hdstW : heap + 1 + q < 2 ^ w := by omega
  let s0 := startState [eta, L, P, heap] mem pos
  let s1 : State := { s0 with mem := Function.update s0.mem heap 0 }
  let s2 : State := { s1 with regs := Function.update s1.regs 4 (heap + 1 + q) }
  have rStore0 : Runs w p ω (.store (.reg 3) (.const 0)) s0 .normal s1 3 :=
    runs_store_iff.mpr ⟨heap, 0, by simp [Expr.eval, s0, startState],
      by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have rDst : Runs w p ω
      (.assign 4 (.bin .add (.bin .add (.reg 3) (.const 1)) (.bin .div (.reg 2) (.const 4))))
      s1 .normal s2 8 :=
    runs_assign_iff.mpr ⟨heap + 1 + q, by
      simp [Expr.eval, BinOp.eval, s1, s0, startState, show 1 < 2 ^ w by omega, hw4,
        show heap + 1 < 2 ^ w by omega, show q < 2 ^ w by omega, hdstW, q],
      rfl, rfl, rfl⟩
  have hdisjC : heap + 1 + q + L ≤ eta ∨ eta + L ≤ heap + 1 + q := by
    rcases hetaDisj with h1 | h2
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  obtain ⟨bodyC, hbodyC, oC, stC, cC, hrCCall, ⟨_, _, _, hargsC, _, hcopied, hframeC⟩, hcC⟩ :=
    hCopy [eta, heap + 1 + q, L] s2.mem s2.pos ω
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl <;> assumption)
      ⟨eta, heap + 1 + q, L, rfl, by omega, by omega, by omega, hdisjC⟩
  simp only [List.cons.injEq, and_true] at hargsC
  rcases hargsC with ⟨rfl, rfl, rfl⟩
  change cC ≤ 17 * L + 10 at hcC
  let s3 : State := { regs := Function.update s2.regs 5 oC.value, mem := stC.mem, pos := stC.pos }
  have rCallC : Runs w p ω (.call 5 copyWords [.reg 0, .reg 4, .reg 1]) s2 .normal s3 (cC + 4) :=
    runs_call_iff.mpr ⟨[eta, heap + 1 + q, L], bodyC, oC, stC, cC,
      by simp [evalArgs, Expr.eval, s2, s1, s0, startState], hbodyC, hrCCall, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
  have rRet : Runs w p ω
      (.ret (.bin .add (.bin .add (.reg 3) (.const 1)) (.bin .mul (.const 2) (.reg 1))))
      s3 (.returned (heap + 1 + 2 * L)) s3 8 :=
    runs_ret_iff.mpr ⟨heap + 1 + 2 * L, by
      simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, startState,
        show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega,
        show heap + 1 < 2 ^ w by omega, show 2 * L < 2 ^ w by omega, hroom],
      rfl, rfl, rfl⟩
  have hrFull : Runs w p ω (updateFailOutputBody copyWords) s0
      (.returned (heap + 1 + 2 * L)) s3 (3 + (8 + ((cC + 4) + 8 + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, rStore0,
      runs_seq_iff.mpr (Or.inr ⟨s2, 8, _, rDst,
      runs_seq_iff.mpr (Or.inr ⟨s3, cC + 4, 8, rCallC, rRet, rfl⟩), rfl⟩), rfl⟩)
  -- Verify memory layout and exact shifted scalar value
  have hs2mem (a : ℕ) : s2.mem a = if a = heap then 0 else mem a := by
    by_cases h : a = heap <;> simp [s2, s1, s0, startState, h]
  have houtFrame : ∀ a, a < heap ∨ heap + 1 + 2 * L ≤ a → s3.mem a = mem a := fun a ha => by
    change stC.mem a = mem a
    rcases ha with hlo | hhi
    · rw [hframeC a (Or.inl (by omega)), hs2mem a, ite_eq_right (by omega)]
    · rw [hframeC a (Or.inr (by omega)), hs2mem a, ite_eq_right (by omega)]
  have hAns : AnswerAt s3.mem heap none := by
    change stC.mem heap = 0
    rw [hframeC heap (Or.inl (by omega)), hs2mem heap, ite_eq_left rfl]
  have hpref0 : ∀ i < q, s3.mem (heap + 1 + i) = 0 := fun i hi => by
    change stC.mem (heap + 1 + i) = 0
    rw [hframeC (heap + 1 + i) (Or.inl (by omega)), hs2mem, ite_eq_right (by omega)]
    exact hz i (by omega)
  have hmidEq : ∀ i < L, s3.mem (heap + 1 + q + i) = mem (eta + i) := fun i hi => by
    change stC.mem (heap + 1 + q + i) = mem (eta + i)
    have hne : eta + i ≠ heap := by rcases hetaDisj with h1 | h2 <;> omega
    rw [hcopied i hi, hs2mem, ite_eq_right hne]
  have hsuff0 : ∀ i < L - q, s3.mem (heap + 1 + q + L + i) = 0 := fun i hi => by
    change stC.mem (heap + 1 + q + L + i) = 0
    rw [hframeC (heap + 1 + q + L + i) (Or.inr (by omega)), hs2mem, ite_eq_right (by omega)]
    have hidx : heap + 1 + q + L + i = heap + 1 + (q + L + i) := by omega
    rw [hidx]; exact hz (q + L + i) (by omega)
  have hvalidOut : Num.Valid s3.mem (heap + 1) 4 (2 * L) := by
    intro i hi
    by_cases h1 : i < q
    · rw [hpref0 i h1]; exact Num.base_pos 4
    · by_cases h2 : i < q + L
      · have hidx : heap + 1 + i = heap + 1 + q + (i - q) := by omega
        rw [hidx, hmidEq (i - q) (by omega)]
        exact hvalid (i - q) (by omega)
      · have hidx : heap + 1 + i = heap + 1 + q + L + (i - q - L) := by omega
        rw [hidx, hsuff0 (i - q - L) (by omega)]
        exact Num.base_pos 4
  have huVal : Num.unsignedVal s3.mem (heap + 1) 4 (2 * L) =
      2 ^ P * Num.unsignedVal mem eta 4 L := by
    rw [show 2 * L = q + (L + (L - q)) by omega,
      unsignedVal_zero_prefix q (L + (L - q)) hpref0,
      unsignedVal_zero_suffix L (L - q) hsuff0,
      unsignedVal_congr L hmidEq]
    unfold Num.base
    rw [← pow_mul, hPeq]
  have hintPos : 0 < Num.intVal mem eta 4 L := by
    unfold Num.fixVal at hpos
    have hpow : (0 : ℝ) < (2 : ℝ) ^ P := by positivity
    have hmul := (div_pos_iff_of_pos_right hpow).mp hpos
    exact_mod_cast hmul
  have huHalf : 2 * Num.unsignedVal mem eta 4 L < Num.capacity 4 L := by
    unfold Num.intVal Num.signedVal at hintPos
    by_contra hge; push Not at hge
    rw [ite_eq_left hge] at hintPos
    have hlt := Num.unsignedVal_lt hvalid
    omega
  have hintOld : Num.intVal mem eta 4 L = (Num.unsignedVal mem eta 4 L : ℤ) := by
    unfold Num.intVal Num.signedVal
    rw [ite_eq_right (by omega), sub_zero]
  have huHalfOut : 2 * Num.unsignedVal s3.mem (heap + 1) 4 (2 * L) < Num.capacity 4 (2 * L) := by
    rw [huVal]
    have hcap2 : Num.capacity 4 (2 * L) = Num.capacity 4 L * Num.capacity 4 L := by
      unfold Num.capacity; rw [two_mul, pow_add]
    have hpowLe : 2 ^ P ≤ Num.capacity 4 L := by
      unfold Num.capacity Num.base; rw [← pow_mul]; exact Nat.pow_le_pow_right (by decide) hPL
    rw [hcap2, show 2 * (2 ^ P * Num.unsignedVal mem eta 4 L) =
        2 ^ P * (2 * Num.unsignedVal mem eta 4 L) by ring]
    exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left huHalf (by positivity))
      (Nat.mul_le_mul_right _ hpowLe)
  have hintNew : Num.intVal s3.mem (heap + 1) 4 (2 * L) =
      (2 : ℤ) ^ P * Num.intVal mem eta 4 L := by
    rw [hintOld]
    unfold Num.intVal Num.signedVal
    rw [ite_eq_right (by omega), sub_zero, huVal]
    push_cast; rfl
  have hScalar : ScalarAt s3.mem (heap + 1) 4 (2 * L) (2 * P) (Num.fixVal mem eta 4 L P) := by
    refine ⟨hvalidOut, ?_⟩
    unfold Num.fixVal
    rw [hintNew, two_mul, pow_add]
    push_cast
    have hpow : (2 : ℝ) ^ P ≠ 0 := by positivity
    field_simp [hpow]
  exact ⟨_, s3, hrFull, by omega, hAns, hScalar, normalizationWithin_self hpos.le, houtFrame⟩

end MinCostFlow.MinRatio
