module

public import MinCostFlow.Scaling.WordPairProgram
public import MinCostFlow.Statement.Problem
import WordRAM.Tactic
import WordRAM.Entry
import Mathlib.Tactic.NormNum

/-!
# Clipping rounded residual costs

The cost-scaling model clips rounded residual costs between `-B^8` and
`B^9`. For a negative value only the lower bound matters, and for a
nonnegative value only the upper bound matters. This procedure therefore
clips the magnitude at the bound selected by the input sign. It writes a
canonical signed pair, allocates two cells, and costs at most 100 steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem clip_negative (z : ℤ) (L H : ℕ) (hz : z < 0) :
    max (-(L : ℤ)) (min z (H : ℤ)) = -((min z.natAbs L : ℕ) : ℤ) := by
  have ha : (z.natAbs : ℤ) = -z := by rw [Int.natCast_natAbs, abs_of_neg hz]
  by_cases hq : z.natAbs ≤ L
  · rw [min_eq_left hq]; omega
  · rw [min_eq_right (by omega : L ≤ z.natAbs)]; omega

private theorem clip_nonnegative (z : ℤ) (L H : ℕ) (hz : ¬ z < 0) :
    max (-(L : ℤ)) (min z (H : ℤ)) = ((min z.natAbs H : ℕ) : ℤ) := by
  have ha : (z.natAbs : ℤ) = z := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
  by_cases hq : z.natAbs ≤ H
  · rw [min_eq_left hq]; omega
  · rw [min_eq_right (by omega : H ≤ z.natAbs)]; omega

/-- Clipping selects the sign's magnitude bound and clears the sign at zero. -/
theorem encodeInt_clip (z : ℤ) (L H : ℕ) :
    let q := min z.natAbs (if z < 0 then L else H)
    encodeInt (max (-(L : ℤ)) (min z (H : ℤ))) =
      [(if z < 0 then 1 else 0) * (if 0 < q then 1 else 0), q] := by
  dsimp only
  by_cases hz : z < 0
  · rw [clip_negative z L H hz]
    simp only [hz, ↓reduceIte, Nat.one_mul]
    by_cases hq : min z.natAbs L = 0
    · simp only [hq, Nat.cast_zero, neg_zero, encodeInt, lt_self_iff_false,
        ↓reduceIte, Int.natAbs_zero]
    · have hn : -((min z.natAbs L : ℕ) : ℤ) < 0 := by omega
      have hp : 0 < min z.natAbs L := by omega
      simp only [encodeInt, hn, hp, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast]
  · rw [clip_nonnegative z L H hz]
    have hn : ¬ ((min z.natAbs H : ℕ) : ℤ) < 0 := by omega
    simp only [hz, hn, ↓reduceIte, Nat.zero_mul, encodeInt, Int.natAbs_natCast]

/-- Write a clipped magnitude with canonical sign. -/
def costClipFinish (writer : ℕ) (magnitude : Expr) : Stmt :=
  .call 6 writer [.bin .mul (.reg 0) (.bin .lt (.const 0) magnitude), magnitude, .reg 4] ;;
  .ret (.reg 6)

/-- Arguments `[sign,magnitude,lowerMagnitude,upperBound,heap]`. -/
def costClipBody (writer : ℕ) : Stmt :=
  .assign 5 (.bin .add (.bin .mul (.reg 2) (.reg 0))
    (.bin .mul (.reg 3) (.bin .sub (.const 1) (.reg 0)))) ;;
  .cond (.bin .lt (.reg 1) (.reg 5))
    (costClipFinish writer (.reg 1)) (costClipFinish writer (.reg 5))

/-- Clipping and the shared canonical pair writer. -/
def costClipModule (b : ℕ) : List Stmt := [costClipBody (b + 1), wordPairBody]

/-- Both magnitude bounds are natural and may be zero. -/
def costClipContract (w : ℕ) (z : ℤ) (L H : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ heap, args = [if z < 0 then 1 else 0, z.natAbs, L, H, heap])
    (fun args _ mem' => ListAt mem' (heapArg args)
      (encodeInt (max (-(L : ℤ)) (min z (H : ℤ)))))
    (fun _ _ => 100) (fun _ _ => 2)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧ out = heapArg args + 2 }

/-- Clipping and writing have no random instructions. -/
theorem costClipModule_noRand (b : ℕ) : ∀ body ∈ costClipModule b, body.NoRand := by
  intro body hb
  simp only [costClipModule, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · simp only [costClipBody, costClipFinish, Stmt.NoRand, and_self]
  · exact wordPairBody_noRand

/-- The machine clips exactly as `CostState.roundedInstance`, including
canonical zero when either clipping bound is zero. -/
theorem costClip_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (costClipModule b)) (z : ℤ) (L H : ℕ) :
    MeetsContract w p b (costClipContract w z L H) := by
  have hpair : p.HasAt (b + 1) wordPairModule := by
    intro i hi
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [costClipModule, wordPairModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 1 (by simp [costClipModule])
  have hk := wordPair_meetsContract (w := w) hpair
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨heap, rfl⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + 2 < 2 ^ w at hspace
  have hzword : z.natAbs < 2 ^ w := hwords _ (by simp)
  have hL : L < 2 ^ w := hwords _ (by simp)
  have hH : H < 2 ^ w := hwords _ (by simp)
  have hh : heap < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  let sign : ℕ := if z < 0 then 1 else 0
  let cap := if z < 0 then L else H
  have hsign : sign < 2 ^ w := by dsimp [sign]; split <;> omega
  have hflip : 1 - sign < 2 ^ w := by dsimp [sign]; split <;> omega
  have hlow : L * sign < 2 ^ w := by dsimp [sign]; split <;> simp only [Nat.mul_one, Nat.mul_zero] <;> omega
  have hhigh : H * (1 - sign) < 2 ^ w := by
    dsimp [sign]; split <;> simp only [Nat.sub_self, Nat.sub_zero, Nat.mul_one, Nat.mul_zero] <;> omega
  have hcap : L * sign + H * (1 - sign) = cap := by
    dsimp [sign, cap]; split <;> simp
  have hcapword : cap < 2 ^ w := by dsimp [cap]; split <;> omega
  have hsum : L * sign + H * (1 - sign) < 2 ^ w := hcap ▸ hcapword
  apply runs_start_le
  unfold costClipBody
  refine runs_seq_assign_le (v := cap) ?_ ?_
  · rw [← hcap]; eval_expr
  · wram_step
    · have hlt : z.natAbs < cap := by simpa [startState] using hcond
      have hencoding := encodeInt_clip z L H
      change encodeInt _ = [sign * (if 0 < min z.natAbs cap then 1 else 0), min z.natAbs cap] at hencoding
      rw [min_eq_left hlt.le] at hencoding
      have hb : (if 0 < z.natAbs then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
      have hp : sign * (if 0 < z.natAbs then 1 else 0) < 2 ^ w := by
        dsimp [sign]; split <;> simp only [Nat.one_mul, Nat.zero_mul] <;> omega
      unfold costClipFinish
      refine runs_seq_call_le hk (vs := [sign * (if 0 < z.natAbs then 1 else 0), z.natAbs, heap])
        (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨⟨_, _, heap, rfl⟩, hzero, hspace⟩
      · intro out memS posS hpost
        have hptr := hpost.2
        change out = heap + 2 at hptr
        have hout : out < 2 ^ w := by omega
        refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
        · change (heap ≤ out ∧ out ≤ heap + 2 ∧ (∀ a < heap, memS a = mem a) ∧
            ZeroFrom memS out ∧ ListAt memS heap (encodeInt _)) ∧ out = heap + 2
          rw [hencoding]
          exact hpost
        · simp only [costClipContract, heapContract, wordPairContract, Expr.size_bin,
            Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil]; omega
    · have hlt : ¬ z.natAbs < cap := by simpa [startState] using hcond
      have hencoding := encodeInt_clip z L H
      change encodeInt _ = [sign * (if 0 < min z.natAbs cap then 1 else 0), min z.natAbs cap] at hencoding
      rw [min_eq_right (Nat.le_of_not_gt hlt)] at hencoding
      have hb : (if 0 < cap then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
      have hp : sign * (if 0 < cap then 1 else 0) < 2 ^ w := by
        dsimp [sign]; split <;> simp only [Nat.one_mul, Nat.zero_mul] <;> omega
      unfold costClipFinish
      refine runs_seq_call_le hk (vs := [sign * (if 0 < cap then 1 else 0), cap, heap])
        (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨⟨_, _, heap, rfl⟩, hzero, hspace⟩
      · intro out memS posS hpost
        have hptr := hpost.2
        change out = heap + 2 at hptr
        have hout : out < 2 ^ w := by omega
        refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
        · change (heap ≤ out ∧ out ≤ heap + 2 ∧ (∀ a < heap, memS a = mem a) ∧
            ZeroFrom memS out ∧ ListAt memS heap (encodeInt _)) ∧ out = heap + 2
          rw [hencoding]
          exact hpost
        · simp only [costClipContract, heapContract, wordPairContract, Expr.size_bin,
            Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil]; omega

/-- All clipping premises hold together for arbitrary values and bounds. -/
theorem exists_costClip_pre (z : ℤ) (L H : ℕ) :
    ∃ w, (∀ x ∈ [if z < 0 then 1 else 0, z.natAbs, L, H, 0], x < 2 ^ w) ∧
      (costClipContract w z L H).pre
        [if z < 0 then 1 else 0, z.natAbs, L, H, 0] (fun _ => 0) := by
  let w := z.natAbs + L + H + 3
  have hw : z.natAbs + L + H + 3 < 2 ^ w := Nat.lt_two_pow_self
  refine ⟨w, ?_, ⟨0, rfl⟩, (fun _ _ => rfl), ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · split <;> omega
    all_goals omega
  · change 0 + 2 < 2 ^ w
    omega

end MinCostFlow.Scaling.Machine
