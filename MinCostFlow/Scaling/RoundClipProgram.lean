module

public import MinCostFlow.Scaling.NearestQuotientProgram
public import MinCostFlow.Scaling.CostClipProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Rounding and clipping a reduced residual cost

The cost-scaling model rounds its integer numerator with a positive
denominator, then clips the resulting integer. This procedure performs
those two operations in order. It allocates four cells including the
rounding pair and costs at most 300 machine steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[sign,magnitude,denominator,lowerMagnitude,upperBound,heap]`. -/
def roundClipBody (round clip : ℕ) : Stmt :=
  .call 6 round [.reg 0, .reg 1, .reg 2, .reg 5] ;;
  .call 7 clip [.load (.reg 5), .load (.bin .add (.reg 5) (.const 1)), .reg 3, .reg 4, .reg 6] ;;
  .ret (.reg 7)

/-- The entry followed by the rounding and clipping modules. -/
def roundClipModule (b : ℕ) : List Stmt :=
  roundClipBody (b + 1) (b + 3) ::
    (nearestQuotientModule (b + 1) ++ costClipModule (b + 3))

/-- The denominator is positive and the rounding adjustment fits a word. -/
def roundClipContract (w : ℕ) (z : ℤ) (d L H : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ heap, args = [if z < 0 then 1 else 0, z.natAbs, d, L, H, heap] ∧
      0 < d ∧ z.natAbs+d/2 < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args + 2)
      (encodeInt (max (-(L : ℤ)) (min (nearestQuotient z d) (H : ℤ)))))
    (fun _ _ => 300) (fun _ _ => 4)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧ out = heapArg args + 4 }

/-- Rounding's output magnitude is its nonnegative integer quotient. -/
theorem nearestQuotient_natAbs (z : ℤ) (d : ℕ) :
    (nearestQuotient z d).natAbs = (z.natAbs + d/2)/d := by
  unfold nearestQuotient
  split <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]

/-- The composed rounding and clipping program uses no random instructions. -/
theorem roundClipModule_noRand (b : ℕ) : ∀ body ∈ roundClipModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [roundClipBody, Stmt.NoRand, and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact nearestQuotientModule_noRand _ body hb
    · exact costClipModule_noRand _ body hb

/-- Rounding followed by clipping computes the exact cost-model operation
with four allocated cells and constant cost. -/
theorem roundClip_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (roundClipModule b)) (z : ℤ) (d L H : ℕ) :
    MeetsContract w p b (roundClipContract w z d L H) := by
  have htail := hasAt_tail hp
  have hround := hasAt_append_left htail
  have hclip : p.HasAt (b + 3) (costClipModule (b + 3)) := by
    have h := hasAt_append_right htail
    simpa only [nearestQuotientModule, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.add_assoc] using h
  have hkR := nearestQuotient_meetsContract (w := w) hround z d
  have hkC := costClip_meetsContract (w := w) hclip (nearestQuotient z d) L H
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨heap, rfl, hdpos, hsum⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + 4 < 2 ^ w at hspace
  have hz : z.natAbs < 2 ^ w := by omega
  have hd : d < 2 ^ w := hwords _ (by simp)
  have hL : L < 2 ^ w := hwords _ (by simp)
  have hH : H < 2 ^ w := hwords _ (by simp)
  have hh : heap < 2 ^ w := by omega
  have hh1 : heap + 1 < 2 ^ w := by omega
  have hh2 : heap + 2 < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have hs : (if z < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hmag : (nearestQuotient z d).natAbs < 2 ^ w := by
    rw [nearestQuotient_natAbs]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) hsum
  have hsign : (if nearestQuotient z d < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  apply runs_start_le
  unfold roundClipBody
  refine runs_seq_call_le hkR (vs := [if z < 0 then 1 else 0, z.natAbs, d, heap])
    (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨heap, rfl, hdpos, hsum⟩, hzero, hh2⟩
  · intro next memR posR hpostR
    obtain ⟨⟨_, _, hframeR, hzeroR, hpairR⟩, hnext⟩ := hpostR
    change next = heap + 2 at hnext
    change (∀ a < heap, memR a = mem a) at hframeR
    change ZeroFrom memR next at hzeroR
    change ListAt memR heap (encodeInt (nearestQuotient z d)) at hpairR
    have hsR : memR heap = if nearestQuotient z d < 0 then 1 else 0 := by
      simpa only [encodeInt, List.getElem_cons_zero, Nat.add_zero] using
        hpairR 0 (by change 0 < 2; decide)
    have hmR : memR (heap + 1) = (nearestQuotient z d).natAbs := by
      simpa only [encodeInt, List.getElem_cons_succ, List.getElem_cons_zero] using
        hpairR 1 (by change 1 < 2; decide)
    have hnextword : next < 2 ^ w := by omega
    refine runs_seq_call_le hkC
      (vs := [if nearestQuotient z d < 0 then 1 else 0, (nearestQuotient z d).natAbs, L, H, next])
      (by eval_expr) ?_ ?_ ?_
    · wram_words
    · refine ⟨⟨next, rfl⟩, hzeroR, ?_⟩
      change next + 2 < 2 ^ w
      omega
    · intro out memC posC hpostC
      obtain ⟨⟨_, _, hframeC, hzeroC, hpairC⟩, hout⟩ := hpostC
      change out = next + 2 at hout
      change (∀ a < next, memC a = memR a) at hframeC
      change ZeroFrom memC out at hzeroC
      change ListAt memC next (encodeInt (max (-(L : ℤ)) (min (nearestQuotient z d) (H : ℤ)))) at hpairC
      have houtword : out < 2 ^ w := by omega
      refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
      · change (heap ≤ out ∧ out ≤ heap + 4 ∧ (∀ a < heap, memC a = mem a) ∧
          ZeroFrom memC out ∧ ListAt memC (heap + 2)
            (encodeInt (max (-(L : ℤ)) (min (nearestQuotient z d) (H : ℤ))))) ∧ out = heap + 4
        refine ⟨⟨by omega, by omega, ?_, hzeroC, ?_⟩, by omega⟩
        · intro a ha
          exact (hframeC a (by omega)).trans (hframeR a ha)
        · simpa only [hnext] using hpairC
      · simp only [roundClipContract, heapContract, nearestQuotientContract, costClipContract,
          argsSize_cons, argsSize_nil, Expr.size_bin, Expr.size_load, Expr.size_reg,
          Expr.size_const]; omega

/-- Every numerator, positive denominator, and clipping bounds have simultaneous witnesses for all
premises together at one sufficiently large width. -/
theorem exists_roundClip_pre (z : ℤ) (d L H : ℕ) (hd : 0 < d) :
    ∃ w, (∀ a ∈ [if z < 0 then 1 else 0, z.natAbs, d, L, H, 0], a < 2 ^ w) ∧
      (roundClipContract w z d L H).pre
        [if z < 0 then 1 else 0, z.natAbs, d, L, H, 0] (fun _ => 0) := by
  let w := z.natAbs + d + L + H + 5
  have hw : z.natAbs + d + L + H + 5 < 2 ^ w := Nat.lt_two_pow_self
  have hhalf := Nat.div_le_self d 2
  refine ⟨w, ?_, ⟨0, rfl, hd, by omega⟩, (fun _ _ => rfl), ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · split <;> omega
    all_goals omega
  · change 0 + 4 < 2 ^ w
    omega

end MinCostFlow.Scaling.Machine
